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
  fun uu___147_390  ->
    match uu___147_390 with
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
  fun uu___148_1735  ->
    match uu___148_1735 with
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
  fun uu___149_1842  ->
    match uu___149_1842 with | [] -> true | uu____1845 -> false
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
                           (let uu___167_3019 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___167_3019.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___167_3019.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____3013)) in
                  (match uu____2983 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___168_3035 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___168_3035.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___168_3035.FStar_Syntax_Syntax.lbeff);
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
                           (let uu___169_3118 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___169_3118.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___169_3118.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_43  -> FStar_Util.Inl _0_43)) in
                    let uu___170_3119 = lb in
                    let uu____3120 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___170_3119.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___170_3119.FStar_Syntax_Syntax.lbeff);
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
                                   ((let uu___171_3577 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___171_3577.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___172_3596 = x in
                                let uu____3597 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___172_3596.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___172_3596.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3597
                                } in
                              ((let uu___173_3605 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___173_3605.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___174_3610 = x in
                                let uu____3611 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___174_3610.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___174_3610.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3611
                                } in
                              ((let uu___175_3619 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___175_3619.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___176_3629 = x in
                                let uu____3630 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___176_3629.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___176_3629.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3630
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___177_3639 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___177_3639.FStar_Syntax_Syntax.p)
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
                          let uu___178_4005 = b in
                          let uu____4006 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___178_4005.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___178_4005.FStar_Syntax_Syntax.index);
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
                        (fun uu___150_4143  ->
                           match uu___150_4143 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____4147 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____4147
                           | f -> f)) in
                 let uu____4151 =
                   let uu___179_4152 = c1 in
                   let uu____4153 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____4153;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___179_4152.FStar_Syntax_Syntax.effect_name);
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
         (fun uu___151_4163  ->
            match uu___151_4163 with
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
                   (fun uu___152_4187  ->
                      match uu___152_4187 with
                      | FStar_Syntax_Syntax.DECREASES uu____4188 -> false
                      | uu____4191 -> true)) in
            let rc1 =
              let uu___180_4193 = rc in
              let uu____4194 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___180_4193.FStar_Syntax_Syntax.residual_effect);
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
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (bytes,uu____4485)) ->
             FStar_Pervasives_Native.Some (FStar_Util.string_of_bytes bytes)
         | uu____4490 -> FStar_Pervasives_Native.None) in
  let arg_as_list f uu____4516 =
    match uu____4516 with
    | (a,uu____4530) ->
        let rec sequence l =
          match l with
          | [] -> FStar_Pervasives_Native.Some []
          | (FStar_Pervasives_Native.None )::uu____4559 ->
              FStar_Pervasives_Native.None
          | (FStar_Pervasives_Native.Some x)::xs ->
              let uu____4576 = sequence xs in
              (match uu____4576 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some xs' ->
                   FStar_Pervasives_Native.Some (x :: xs')) in
        let uu____4596 = FStar_Syntax_Util.list_elements a in
        (match uu____4596 with
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some elts ->
             let uu____4614 =
               FStar_List.map
                 (fun x  ->
                    let uu____4624 = FStar_Syntax_Syntax.as_arg x in
                    f uu____4624) elts in
             sequence uu____4614) in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4662 = f a in FStar_Pervasives_Native.Some uu____4662
    | uu____4663 -> FStar_Pervasives_Native.None in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4713 = f a0 a1 in FStar_Pervasives_Native.Some uu____4713
    | uu____4714 -> FStar_Pervasives_Native.None in
  let unary_op as_a f r args =
    let uu____4763 = FStar_List.map as_a args in lift_unary (f r) uu____4763 in
  let binary_op as_a f r args =
    let uu____4819 = FStar_List.map as_a args in lift_binary (f r) uu____4819 in
  let as_primitive_step uu____4843 =
    match uu____4843 with
    | (l,arity,f) ->
        { name = l; arity; strong_reduction_ok = true; interpretation = f } in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  -> fun x  -> let uu____4891 = f x in int_as_const r uu____4891) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  -> let uu____4919 = f x y in int_as_const r uu____4919) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  -> fun x  -> let uu____4940 = f x in bool_as_const r uu____4940) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  -> let uu____4968 = f x y in bool_as_const r uu____4968) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  -> let uu____4996 = f x y in string_as_const r uu____4996) in
  let list_of_string' rng s =
    let name l =
      let uu____5010 =
        let uu____5011 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
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
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in int_as_const rng r in
  let string_concat' rng args =
    match args with
    | a1::a2::[] ->
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
  let string_of_bool1 rng b =
    string_as_const rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____5157 = FStar_Util.string_of_int i in
    string_as_const rng uu____5157 in
  let string_of_bool2 rng b =
    string_as_const rng (if b then "true" else "false") in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r in
  let range_of1 uu____5187 args =
    match args with
    | uu____5199::(t,uu____5201)::[] ->
        let uu____5230 = term_of_range t.FStar_Syntax_Syntax.pos in
        FStar_Pervasives_Native.Some uu____5230
    | uu____5235 -> FStar_Pervasives_Native.None in
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
          (let uu___181_5321 = t in
           {
             FStar_Syntax_Syntax.n = (uu___181_5321.FStar_Syntax_Syntax.n);
             FStar_Syntax_Syntax.pos = r1;
             FStar_Syntax_Syntax.vars =
               (uu___181_5321.FStar_Syntax_Syntax.vars)
           })
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
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r1 =
               let uu____5469 = FStar_Range.mk_pos from_l from_c in
               let uu____5470 = FStar_Range.mk_pos to_l to_c in
               FStar_Range.mk_range fn1 uu____5469 uu____5470 in
             let uu____5471 = term_of_range r1 in
             FStar_Pervasives_Native.Some uu____5471
         | uu____5476 -> FStar_Pervasives_Native.None)
    | uu____5497 -> FStar_Pervasives_Native.None in
  let decidable_eq neg rng args =
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) rng in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) rng in
    match args with
    | (_typ,uu____5527)::(a1,uu____5529)::(a2,uu____5531)::[] ->
        let uu____5568 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____5568 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____5581 -> FStar_Pervasives_Native.None)
    | uu____5582 -> failwith "Unexpected number of arguments" in
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
                                      (FStar_Parser_Const.string_compare,
                                        (Prims.parse_int "2"),
                                        (binary_op arg_as_string
                                           string_compare'))
                                        :: uu____5855 in
                                    (FStar_Parser_Const.string_of_bool_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_bool string_of_bool2))
                                      :: uu____5840 in
                                  (FStar_Parser_Const.string_of_int_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_int string_of_int2)) ::
                                    uu____5825 in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____5810 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
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
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
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
let equality_ops: primitive_step Prims.list =
  let interp_prop r args =
    match args with
    | (_typ,uu____7108)::(a1,uu____7110)::(a2,uu____7112)::[] ->
        let uu____7149 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____7149 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___182_7155 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___182_7155.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___182_7155.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___183_7159 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___183_7159.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___183_7159.FStar_Syntax_Syntax.vars)
                })
         | uu____7160 -> FStar_Pervasives_Native.None)
    | (_typ,uu____7162)::uu____7163::(a1,uu____7165)::(a2,uu____7167)::[] ->
        let uu____7216 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____7216 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___182_7222 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___182_7222.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___182_7222.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___183_7226 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___183_7226.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___183_7226.FStar_Syntax_Syntax.vars)
                })
         | uu____7227 -> FStar_Pervasives_Native.None)
    | uu____7228 -> failwith "Unexpected number of arguments" in
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
      let uu____7241 =
        FStar_All.pipe_left Prims.op_Negation
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
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____7285 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps in
                  (match uu____7285 with
                   | FStar_Pervasives_Native.None  -> tm
                   | FStar_Pervasives_Native.Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then tm
                       else
                         (let uu____7298 =
                            prim_step.interpretation
                              head1.FStar_Syntax_Syntax.pos args in
                          match uu____7298 with
                          | FStar_Pervasives_Native.None  -> tm
                          | FStar_Pervasives_Native.Some reduced -> reduced))
              | uu____7302 -> tm))
let reduce_equality:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___184_7313 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___184_7313.tcenv);
           delta_level = (uu___184_7313.delta_level);
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
        let uu___185_7337 = t in
        {
          FStar_Syntax_Syntax.n = (uu___185_7337.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___185_7337.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid ->
            FStar_Pervasives_Native.Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid ->
            FStar_Pervasives_Native.Some false
        | uu____7354 -> FStar_Pervasives_Native.None in
      let simplify arg = ((simp_t (FStar_Pervasives_Native.fst arg)), arg) in
      let tm1 = reduce_primops cfg tm in
      let uu____7394 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps) in
      if uu____7394
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
                    -> arg
                | (FStar_Pervasives_Native.Some (false ),uu____7619)::uu____7620::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____7683::(FStar_Pervasives_Native.Some (false
                               ),uu____7684)::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____7747 -> tm1)
             else
               (let uu____7763 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
                if uu____7763
                then
                  let uu____7764 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____7764 with
                  | (FStar_Pervasives_Native.Some (true ),uu____7819)::uu____7820::[]
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
                       FStar_Parser_Const.imp_lid in
                   if uu____8099
                   then
                     let uu____8100 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____8100 with
                     | uu____8155::(FStar_Pervasives_Native.Some (true
                                    ),uu____8156)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____8219)::uu____8220::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____8283)::
                         (uu____8284,(arg,uu____8286))::[] -> arg
                     | (uu____8351,(p,uu____8353))::(uu____8354,(q,uu____8356))::[]
                         ->
                         let uu____8421 = FStar_Syntax_Util.term_eq p q in
                         (if uu____8421
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____8423 -> tm1
                   else
                     (let uu____8439 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____8439
                      then
                        let uu____8440 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____8440 with
                        | (FStar_Pervasives_Native.Some (true ),uu____8495)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____8534)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____8573 -> tm1
                      else
                        (let uu____8589 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
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
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____8612::[],body,uu____8614) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
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
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____8757::[],body,uu____8759) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
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
                    -> arg
                | (FStar_Pervasives_Native.Some (false ),uu____9095)::uu____9096::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____9159::(FStar_Pervasives_Native.Some (false
                               ),uu____9160)::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____9223 -> tm1)
             else
               (let uu____9239 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
                if uu____9239
                then
                  let uu____9240 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____9240 with
                  | (FStar_Pervasives_Native.Some (true ),uu____9295)::uu____9296::[]
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
                       FStar_Parser_Const.imp_lid in
                   if uu____9575
                   then
                     let uu____9576 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____9576 with
                     | uu____9631::(FStar_Pervasives_Native.Some (true
                                    ),uu____9632)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____9695)::uu____9696::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____9759)::
                         (uu____9760,(arg,uu____9762))::[] -> arg
                     | (uu____9827,(p,uu____9829))::(uu____9830,(q,uu____9832))::[]
                         ->
                         let uu____9897 = FStar_Syntax_Util.term_eq p q in
                         (if uu____9897
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____9899 -> tm1
                   else
                     (let uu____9915 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____9915
                      then
                        let uu____9916 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____9916 with
                        | (FStar_Pervasives_Native.Some (true ),uu____9971)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____10010)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____10049 -> tm1
                      else
                        (let uu____10065 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
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
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____10088::[],body,uu____10090) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
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
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____10233::[],body,uu____10235) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
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
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____10312::[],body,uu____10314) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____10341 -> tm1)
                                   | uu____10344 -> tm1)
                              | uu____10345 -> tm1
                            else reduce_equality cfg tm1)))))
         | uu____10355 -> tm1)
let is_norm_request:
  'Auu____10362 .
    FStar_Syntax_Syntax.term -> 'Auu____10362 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10375 =
        let uu____10382 =
          let uu____10383 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10383.FStar_Syntax_Syntax.n in
        (uu____10382, args) in
      match uu____10375 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10389::uu____10390::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10394::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10399::uu____10400::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10403 -> false
let get_norm_request:
  'Auu____10416 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10416) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let unembed_step s1 =
          let uu____10458 =
            let uu____10459 = FStar_Syntax_Util.un_uinst s1 in
            uu____10459.FStar_Syntax_Syntax.n in
          match uu____10458 with
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
              let names2 = FStar_Syntax_Embeddings.unembed_string_list names1 in
              let lids =
                FStar_All.pipe_right names2
                  (FStar_List.map FStar_Ident.lid_of_str) in
              UnfoldOnly lids
          | uu____10510 -> failwith "Not an embedded `Prims.step`" in
        FStar_Syntax_Embeddings.unembed_list unembed_step s in
      match args with
      | uu____10517::(tm,uu____10519)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____10542)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____10557)::uu____10558::(tm,uu____10560)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____10600 =
              let uu____10603 = full_norm steps in parse_steps uu____10603 in
            Beta :: uu____10600 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____10612 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___153_10630  ->
    match uu___153_10630 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.pos = uu____10633;
           FStar_Syntax_Syntax.vars = uu____10634;_},uu____10635,uu____10636))::uu____10637
        -> true
    | uu____10644 -> false
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
            (fun uu____10779  ->
               let uu____10780 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____10781 = FStar_Syntax_Print.term_to_string t1 in
               let uu____10782 =
                 let uu____10783 =
                   let uu____10786 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____10786 in
                 stack_to_string uu____10783 in
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
               let uu____10851 =
                 let uu____10852 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____10853 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____10852 uu____10853 in
               failwith uu____10851
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
               let args1 = closures_as_args_delayed cfg env args in
               let hd2 = closure_as_term cfg env hd1 in
               let t2 =
                 let uu___186_10923 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___186_10923.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___186_10923.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____10956 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____10956) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___187_10964 = cfg in
                 let uu____10965 =
                   FStar_List.filter
                     (fun uu___154_10968  ->
                        match uu___154_10968 with
                        | UnfoldOnly uu____10969 -> false
                        | NoDeltaSteps  -> false
                        | uu____10972 -> true) cfg.steps in
                 {
                   steps = uu____10965;
                   tcenv = (uu___187_10964.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___187_10964.primitive_steps)
                 } in
               let uu____10973 = get_norm_request (norm cfg' env []) args in
               (match uu____10973 with
                | (s,tm) ->
                    let delta_level =
                      let uu____10989 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___155_10994  ->
                                match uu___155_10994 with
                                | UnfoldUntil uu____10995 -> true
                                | UnfoldOnly uu____10996 -> true
                                | uu____10999 -> false)) in
                      if uu____10989
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___188_11004 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___188_11004.tcenv);
                        delta_level;
                        primitive_steps = (uu___188_11004.primitive_steps)
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
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11026;
                  FStar_Syntax_Syntax.vars = uu____11027;_},a1::a2::rest)
               ->
               let uu____11075 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11075 with
                | (hd1,uu____11091) ->
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
                    (FStar_Const.Const_reflect uu____11156);
                  FStar_Syntax_Syntax.pos = uu____11157;
                  FStar_Syntax_Syntax.vars = uu____11158;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____11190 = FStar_List.tl stack1 in
               norm cfg env uu____11190 (FStar_Pervasives_Native.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11193;
                  FStar_Syntax_Syntax.vars = uu____11194;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____11226 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11226 with
                | (reify_head,uu____11242) ->
                    let a1 =
                      let uu____11264 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (FStar_Pervasives_Native.fst a) in
                      FStar_Syntax_Subst.compress uu____11264 in
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
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11313 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____11313
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11320 =
                 FStar_All.pipe_right cfg.steps
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
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___156_11344  ->
                         match uu___156_11344 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
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
                           FStar_Parser_Const.false_lid)) in
                 if uu____11347
                 then false
                 else
                   (let uu____11349 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___157_11356  ->
                              match uu___157_11356 with
                              | UnfoldOnly uu____11357 -> true
                              | uu____11360 -> false)) in
                    match uu____11349 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11364 -> should_delta) in
               (log cfg
                  (fun uu____11372  ->
                     let uu____11373 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11374 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____11375 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11373 uu____11374 uu____11375);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack1 t1
                else
                  (let r_env =
                     let uu____11378 = FStar_Syntax_Syntax.range_of_fv f in
                     FStar_TypeChecker_Env.set_range cfg.tcenv uu____11378 in
                   let uu____11379 =
                     FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                       r_env
                       (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   match uu____11379 with
                   | FStar_Pervasives_Native.None  ->
                       (log cfg
                          (fun uu____11392  ->
                             FStar_Util.print "Tm_fvar case 2\n" []);
                        rebuild cfg env stack1 t1)
                   | FStar_Pervasives_Native.Some (us,t2) ->
                       (log cfg
                          (fun uu____11403  ->
                             let uu____11404 =
                               FStar_Syntax_Print.term_to_string t0 in
                             let uu____11405 =
                               FStar_Syntax_Print.term_to_string t2 in
                             FStar_Util.print2 ">>> Unfolded %s to %s\n"
                               uu____11404 uu____11405);
                        (let t3 =
                           let uu____11407 =
                             FStar_All.pipe_right cfg.steps
                               (FStar_List.contains
                                  (UnfoldUntil
                                     FStar_Syntax_Syntax.Delta_constant)) in
                           if uu____11407
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
                           | (UnivArgs (us',uu____11417))::stack2 ->
                               let env1 =
                                 FStar_All.pipe_right us'
                                   (FStar_List.fold_left
                                      (fun env1  ->
                                         fun u  -> (Univ u) :: env1) env) in
                               norm cfg env1 stack2 t3
                           | uu____11440 when
                               FStar_All.pipe_right cfg.steps
                                 (FStar_List.contains EraseUniverses)
                               -> norm cfg env stack1 t3
                           | uu____11441 ->
                               let uu____11442 =
                                 let uu____11443 =
                                   FStar_Syntax_Print.lid_to_string
                                     (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                 FStar_Util.format1
                                   "Impossible: missing universe instantiation on %s"
                                   uu____11443 in
                               failwith uu____11442
                         else norm cfg env stack1 t3))))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11446 = lookup_bvar env x in
               (match uu____11446 with
                | Univ uu____11447 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11472 = FStar_ST.op_Bang r in
                      (match uu____11472 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11553  ->
                                 let uu____11554 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____11555 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11554
                                   uu____11555);
                            (let uu____11556 =
                               let uu____11557 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____11557.FStar_Syntax_Syntax.n in
                             match uu____11556 with
                             | FStar_Syntax_Syntax.Tm_abs uu____11560 ->
                                 norm cfg env2 stack1 t'
                             | uu____11577 -> rebuild cfg env2 stack1 t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____11629)::uu____11630 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11639)::uu____11640 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11650,uu____11651))::stack_rest ->
                    (match c with
                     | Univ uu____11655 -> norm cfg (c :: env) stack_rest t1
                     | uu____11656 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____11661::[] ->
                              (match lopt with
                               | FStar_Pervasives_Native.None  when
                                   FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____11677  ->
                                         let uu____11678 =
                                           closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____11678);
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
                                           (fun uu___158_11683  ->
                                              match uu___158_11683 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____11684 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____11688  ->
                                         let uu____11689 =
                                           closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____11689);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____11690 when
                                   (FStar_All.pipe_right cfg.steps
                                      (FStar_List.contains Reify))
                                     ||
                                     (FStar_All.pipe_right cfg.steps
                                        (FStar_List.contains CheckNoUvars))
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____11693 ->
                                   let cfg1 =
                                     let uu___189_11697 = cfg in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___189_11697.tcenv);
                                       delta_level =
                                         (uu___189_11697.delta_level);
                                       primitive_steps =
                                         (uu___189_11697.primitive_steps)
                                     } in
                                   let uu____11698 =
                                     closure_as_term cfg1 env t1 in
                                   rebuild cfg1 env stack1 uu____11698)
                          | uu____11699::tl1 ->
                              (log cfg
                                 (fun uu____11718  ->
                                    let uu____11719 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11719);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___190_11749 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___190_11749.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____11810  ->
                          let uu____11811 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11811);
                     norm cfg env stack2 t1)
                | (Debug uu____11812)::uu____11813 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11820 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11820
                    else
                      (let uu____11822 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11822 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11846  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11862 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11862
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11872 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11872)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___191_11877 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___191_11877.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___191_11877.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11878 -> lopt in
                           (log cfg
                              (fun uu____11884  ->
                                 let uu____11885 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11885);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___192_11898 = cfg in
                               let uu____11899 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___192_11898.steps);
                                 tcenv = (uu___192_11898.tcenv);
                                 delta_level = (uu___192_11898.delta_level);
                                 primitive_steps = uu____11899
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____11908)::uu____11909 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11916 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11916
                    else
                      (let uu____11918 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11918 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11942  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11958 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11958
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11968 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11968)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___191_11973 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___191_11973.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___191_11973.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11974 -> lopt in
                           (log cfg
                              (fun uu____11980  ->
                                 let uu____11981 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11981);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___192_11994 = cfg in
                               let uu____11995 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___192_11994.steps);
                                 tcenv = (uu___192_11994.tcenv);
                                 delta_level = (uu___192_11994.delta_level);
                                 primitive_steps = uu____11995
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____12004)::uu____12005 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12016 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12016
                    else
                      (let uu____12018 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12018 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12042  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12058 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12058
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12068 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12068)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___191_12073 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___191_12073.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___191_12073.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12074 -> lopt in
                           (log cfg
                              (fun uu____12080  ->
                                 let uu____12081 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12081);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___192_12094 = cfg in
                               let uu____12095 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___192_12094.steps);
                                 tcenv = (uu___192_12094.tcenv);
                                 delta_level = (uu___192_12094.delta_level);
                                 primitive_steps = uu____12095
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____12104)::uu____12105 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12114 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12114
                    else
                      (let uu____12116 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12116 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12140  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12156 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12156
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12166 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12166)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___191_12171 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___191_12171.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___191_12171.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12172 -> lopt in
                           (log cfg
                              (fun uu____12178  ->
                                 let uu____12179 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12179);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___192_12192 = cfg in
                               let uu____12193 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___192_12192.steps);
                                 tcenv = (uu___192_12192.tcenv);
                                 delta_level = (uu___192_12192.delta_level);
                                 primitive_steps = uu____12193
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____12202)::uu____12203 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12218 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12218
                    else
                      (let uu____12220 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12220 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12244  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12260 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12260
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12270 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12270)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___191_12275 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___191_12275.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___191_12275.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12276 -> lopt in
                           (log cfg
                              (fun uu____12282  ->
                                 let uu____12283 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12283);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___192_12296 = cfg in
                               let uu____12297 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___192_12296.steps);
                                 tcenv = (uu___192_12296.tcenv);
                                 delta_level = (uu___192_12296.delta_level);
                                 primitive_steps = uu____12297
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12306 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12306
                    else
                      (let uu____12308 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12308 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12332  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12348 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12348
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12358 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12358)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___191_12363 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___191_12363.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___191_12363.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12364 -> lopt in
                           (log cfg
                              (fun uu____12370  ->
                                 let uu____12371 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12371);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___192_12384 = cfg in
                               let uu____12385 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___192_12384.steps);
                                 tcenv = (uu___192_12384.tcenv);
                                 delta_level = (uu___192_12384.delta_level);
                                 primitive_steps = uu____12385
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
                      (fun uu____12432  ->
                         fun stack2  ->
                           match uu____12432 with
                           | (a,aq) ->
                               let uu____12444 =
                                 let uu____12445 =
                                   let uu____12452 =
                                     let uu____12453 =
                                       let uu____12472 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____12472, false) in
                                     Clos uu____12453 in
                                   (uu____12452, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____12445 in
                               uu____12444 :: stack2) args) in
               (log cfg
                  (fun uu____12524  ->
                     let uu____12525 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12525);
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
                             ((let uu___193_12549 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___193_12549.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___193_12549.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____12550 ->
                      let uu____12555 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12555)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____12558 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____12558 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____12583 =
                          let uu____12584 =
                            let uu____12591 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___194_12593 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___194_12593.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___194_12593.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12591) in
                          FStar_Syntax_Syntax.Tm_refine uu____12584 in
                        mk uu____12583 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____12612 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____12612
               else
                 (let uu____12614 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____12614 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12622 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12634  -> Dummy :: env1) env) in
                        norm_comp cfg uu____12622 c1 in
                      let t2 =
                        let uu____12644 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____12644 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____12703)::uu____12704 -> norm cfg env stack1 t11
                | (Arg uu____12713)::uu____12714 -> norm cfg env stack1 t11
                | (App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____12723;
                       FStar_Syntax_Syntax.vars = uu____12724;_},uu____12725,uu____12726))::uu____12727
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____12734)::uu____12735 ->
                    norm cfg env stack1 t11
                | uu____12744 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____12748  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____12765 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____12765
                        | FStar_Util.Inr c ->
                            let uu____12773 = norm_comp cfg env c in
                            FStar_Util.Inr uu____12773 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____12779 =
                        let uu____12780 =
                          let uu____12781 =
                            let uu____12808 = FStar_Syntax_Util.unascribe t12 in
                            (uu____12808, (tc1, tacopt1), l) in
                          FStar_Syntax_Syntax.Tm_ascribed uu____12781 in
                        mk uu____12780 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____12779)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____12884,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____12885;
                               FStar_Syntax_Syntax.lbunivs = uu____12886;
                               FStar_Syntax_Syntax.lbtyp = uu____12887;
                               FStar_Syntax_Syntax.lbeff = uu____12888;
                               FStar_Syntax_Syntax.lbdef = uu____12889;_}::uu____12890),uu____12891)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____12927 =
                 (let uu____12930 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____12930) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____12932 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____12932))) in
               if uu____12927
               then
                 let env1 =
                   let uu____12936 =
                     let uu____12937 =
                       let uu____12956 =
                         FStar_Util.mk_ref FStar_Pervasives_Native.None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____12956,
                         false) in
                     Clos uu____12937 in
                   uu____12936 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____13008 =
                    let uu____13013 =
                      let uu____13014 =
                        let uu____13015 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____13015
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____13014] in
                    FStar_Syntax_Subst.open_term uu____13013 body in
                  match uu____13008 with
                  | (bs,body1) ->
                      let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                      let lbname =
                        let x =
                          let uu____13029 = FStar_List.hd bs in
                          FStar_Pervasives_Native.fst uu____13029 in
                        FStar_Util.Inl
                          (let uu___195_13039 = x in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___195_13039.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___195_13039.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = ty
                           }) in
                      let lb1 =
                        let uu___196_13041 = lb in
                        let uu____13042 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = lbname;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___196_13041.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = ty;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___196_13041.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____13042
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____13059  -> Dummy :: env1)
                             env) in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let ((true ,lbs),body) when
               FStar_List.contains CompressUvars cfg.steps ->
               let uu____13082 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____13082 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____13118 =
                               let uu___197_13119 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___197_13119.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___197_13119.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____13118 in
                           let uu____13120 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____13120 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____13140 =
                                   FStar_List.map (fun uu____13144  -> Dummy)
                                     lbs1 in
                                 let uu____13145 =
                                   let uu____13148 =
                                     FStar_List.map
                                       (fun uu____13156  -> Dummy) xs1 in
                                   FStar_List.append uu____13148 env in
                                 FStar_List.append uu____13140 uu____13145 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13168 =
                                       let uu___198_13169 = rc in
                                       let uu____13170 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___198_13169.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13170;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___198_13169.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____13168
                                 | uu____13177 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___199_13181 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___199_13181.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___199_13181.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____13185 =
                        FStar_List.map (fun uu____13189  -> Dummy) lbs2 in
                      FStar_List.append uu____13185 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____13191 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____13191 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___200_13207 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___200_13207.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___200_13207.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____13234 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____13234
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13253 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13304  ->
                        match uu____13304 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____13377 =
                                let uu___201_13378 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___201_13378.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___201_13378.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____13377 in
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
               (match uu____13253 with
                | (rec_env,memos,uu____13506) ->
                    let uu____13535 =
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
                             let uu____13940 =
                               let uu____13941 =
                                 let uu____13960 =
                                   FStar_Util.mk_ref
                                     FStar_Pervasives_Native.None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____13960, false) in
                               Clos uu____13941 in
                             uu____13940 :: env1)
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
                             FStar_Syntax_Syntax.pos = uu____14028;
                             FStar_Syntax_Syntax.vars = uu____14029;_},uu____14030,uu____14031))::uu____14032
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____14039 -> false in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____14049 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____14049
                        then
                          let uu___202_14050 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___202_14050.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps =
                              (uu___202_14050.primitive_steps)
                          }
                        else
                          (let uu___203_14052 = cfg in
                           {
                             steps =
                               (FStar_List.append [Exclude Zeta] cfg.steps);
                             tcenv = (uu___203_14052.tcenv);
                             delta_level = (uu___203_14052.delta_level);
                             primitive_steps =
                               (uu___203_14052.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____14054 =
                         let uu____14055 = FStar_Syntax_Subst.compress head1 in
                         uu____14055.FStar_Syntax_Syntax.n in
                       match uu____14054 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____14073 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____14073 with
                            | (uu____14074,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____14080 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____14088 =
                                         let uu____14089 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____14089.FStar_Syntax_Syntax.n in
                                       match uu____14088 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____14095,uu____14096))
                                           ->
                                           let uu____14105 =
                                             let uu____14106 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____14106.FStar_Syntax_Syntax.n in
                                           (match uu____14105 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____14112,msrc,uu____14114))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____14123 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14123
                                            | uu____14124 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____14125 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____14126 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____14126 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___204_14131 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___204_14131.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___204_14131.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___204_14131.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____14132 =
                                            FStar_List.tl stack1 in
                                          let uu____14133 =
                                            let uu____14134 =
                                              let uu____14137 =
                                                let uu____14138 =
                                                  let uu____14151 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____14151) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____14138 in
                                              FStar_Syntax_Syntax.mk
                                                uu____14137 in
                                            uu____14134
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____14132
                                            uu____14133
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____14167 =
                                            let uu____14168 = is_return body in
                                            match uu____14168 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____14172;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____14173;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____14178 -> false in
                                          if uu____14167
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
                                               let uu____14202 =
                                                 let uu____14205 =
                                                   let uu____14206 =
                                                     let uu____14223 =
                                                       let uu____14226 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____14226] in
                                                     (uu____14223, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc)) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____14206 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____14205 in
                                               uu____14202
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____14242 =
                                                 let uu____14243 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____14243.FStar_Syntax_Syntax.n in
                                               match uu____14242 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____14249::uu____14250::[])
                                                   ->
                                                   let uu____14257 =
                                                     let uu____14260 =
                                                       let uu____14261 =
                                                         let uu____14268 =
                                                           let uu____14271 =
                                                             let uu____14272
                                                               =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____14272 in
                                                           let uu____14273 =
                                                             let uu____14276
                                                               =
                                                               let uu____14277
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____14277 in
                                                             [uu____14276] in
                                                           uu____14271 ::
                                                             uu____14273 in
                                                         (bind1, uu____14268) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____14261 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____14260 in
                                                   uu____14257
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____14285 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____14291 =
                                                 let uu____14294 =
                                                   let uu____14295 =
                                                     let uu____14310 =
                                                       let uu____14313 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____14314 =
                                                         let uu____14317 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____14318 =
                                                           let uu____14321 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____14322 =
                                                             let uu____14325
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____14326
                                                               =
                                                               let uu____14329
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____14330
                                                                 =
                                                                 let uu____14333
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____14333] in
                                                               uu____14329 ::
                                                                 uu____14330 in
                                                             uu____14325 ::
                                                               uu____14326 in
                                                           uu____14321 ::
                                                             uu____14322 in
                                                         uu____14317 ::
                                                           uu____14318 in
                                                       uu____14313 ::
                                                         uu____14314 in
                                                     (bind_inst, uu____14310) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____14295 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____14294 in
                                               uu____14291
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____14341 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____14341 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____14365 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____14365 with
                            | (uu____14366,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____14395 =
                                        let uu____14396 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____14396.FStar_Syntax_Syntax.n in
                                      match uu____14395 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____14402) -> t4
                                      | uu____14407 -> head2 in
                                    let uu____14408 =
                                      let uu____14409 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____14409.FStar_Syntax_Syntax.n in
                                    match uu____14408 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____14415 ->
                                        FStar_Pervasives_Native.None in
                                  let uu____14416 = maybe_extract_fv head2 in
                                  match uu____14416 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____14426 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____14426
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____14431 =
                                          maybe_extract_fv head3 in
                                        match uu____14431 with
                                        | FStar_Pervasives_Native.Some
                                            uu____14436 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____14437 ->
                                            FStar_Pervasives_Native.Some
                                              false in
                                      (head3, action_unfolded)
                                  | uu____14442 ->
                                      (head2, FStar_Pervasives_Native.None) in
                                ((let is_arg_impure uu____14457 =
                                    match uu____14457 with
                                    | (e,q) ->
                                        let uu____14464 =
                                          let uu____14465 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____14465.FStar_Syntax_Syntax.n in
                                        (match uu____14464 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____14480 -> false) in
                                  let uu____14481 =
                                    let uu____14482 =
                                      let uu____14489 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____14489 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____14482 in
                                  if uu____14481
                                  then
                                    let uu____14494 =
                                      let uu____14495 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____14495 in
                                    failwith uu____14494
                                  else ());
                                 (let uu____14497 =
                                    maybe_unfold_action head_app in
                                  match uu____14497 with
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
                                      let uu____14536 = FStar_List.tl stack1 in
                                      norm cfg env uu____14536 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____14550 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____14550 in
                           let uu____14551 = FStar_List.tl stack1 in
                           norm cfg env uu____14551 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____14672  ->
                                     match uu____14672 with
                                     | (pat,wopt,tm) ->
                                         let uu____14720 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____14720))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____14752 = FStar_List.tl stack1 in
                           norm cfg env uu____14752 tm
                       | uu____14753 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.pos = uu____14762;
                             FStar_Syntax_Syntax.vars = uu____14763;_},uu____14764,uu____14765))::uu____14766
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____14773 -> false in
                    if should_reify
                    then
                      let uu____14774 = FStar_List.tl stack1 in
                      let uu____14775 =
                        let uu____14776 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____14776 in
                      norm cfg env uu____14774 uu____14775
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____14779 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____14779
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___205_14788 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___205_14788.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___205_14788.primitive_steps)
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
                | uu____14790 ->
                    (match stack1 with
                     | uu____14791::uu____14792 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled
                              (l,r,uu____14797) ->
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
                          | uu____14822 -> norm cfg env stack1 head1)
                     | [] ->
                         let head2 = norm cfg env [] head1 in
                         let m1 =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               let uu____14836 =
                                 norm_pattern_args cfg env args in
                               FStar_Syntax_Syntax.Meta_pattern uu____14836
                           | uu____14847 -> m in
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
              let uu____14859 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____14859 with
              | (uu____14860,return_repr) ->
                  let return_inst =
                    let uu____14869 =
                      let uu____14870 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____14870.FStar_Syntax_Syntax.n in
                    match uu____14869 with
                    | FStar_Syntax_Syntax.Tm_uinst
                        (return_tm,uu____14876::[]) ->
                        let uu____14883 =
                          let uu____14886 =
                            let uu____14887 =
                              let uu____14894 =
                                let uu____14897 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____14897] in
                              (return_tm, uu____14894) in
                            FStar_Syntax_Syntax.Tm_uinst uu____14887 in
                          FStar_Syntax_Syntax.mk uu____14886 in
                        uu____14883 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____14905 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____14908 =
                    let uu____14911 =
                      let uu____14912 =
                        let uu____14927 =
                          let uu____14930 = FStar_Syntax_Syntax.as_arg t in
                          let uu____14931 =
                            let uu____14934 = FStar_Syntax_Syntax.as_arg e in
                            [uu____14934] in
                          uu____14930 :: uu____14931 in
                        (return_inst, uu____14927) in
                      FStar_Syntax_Syntax.Tm_app uu____14912 in
                    FStar_Syntax_Syntax.mk uu____14911 in
                  uu____14908 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____14943 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____14943 with
               | FStar_Pervasives_Native.None  ->
                   let uu____14946 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____14946
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____14947;
                     FStar_TypeChecker_Env.mtarget = uu____14948;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____14949;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____14960;
                     FStar_TypeChecker_Env.mtarget = uu____14961;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____14962;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____14980 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____14980)
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
                (fun uu____15036  ->
                   match uu____15036 with
                   | (a,imp) ->
                       let uu____15047 = norm cfg env [] a in
                       (uu____15047, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___206_15064 = comp1 in
            let uu____15067 =
              let uu____15068 =
                let uu____15077 = norm cfg env [] t in
                let uu____15078 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____15077, uu____15078) in
              FStar_Syntax_Syntax.Total uu____15068 in
            {
              FStar_Syntax_Syntax.n = uu____15067;
              FStar_Syntax_Syntax.pos =
                (uu___206_15064.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___206_15064.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___207_15093 = comp1 in
            let uu____15096 =
              let uu____15097 =
                let uu____15106 = norm cfg env [] t in
                let uu____15107 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____15106, uu____15107) in
              FStar_Syntax_Syntax.GTotal uu____15097 in
            {
              FStar_Syntax_Syntax.n = uu____15096;
              FStar_Syntax_Syntax.pos =
                (uu___207_15093.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___207_15093.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____15159  ->
                      match uu____15159 with
                      | (a,i) ->
                          let uu____15170 = norm cfg env [] a in
                          (uu____15170, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___159_15181  ->
                      match uu___159_15181 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____15185 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____15185
                      | f -> f)) in
            let uu___208_15189 = comp1 in
            let uu____15192 =
              let uu____15193 =
                let uu___209_15194 = ct in
                let uu____15195 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____15196 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____15199 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____15195;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___209_15194.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____15196;
                  FStar_Syntax_Syntax.effect_args = uu____15199;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____15193 in
            {
              FStar_Syntax_Syntax.n = uu____15192;
              FStar_Syntax_Syntax.pos =
                (uu___208_15189.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___208_15189.FStar_Syntax_Syntax.vars)
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
            (let uu___210_15217 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___210_15217.tcenv);
               delta_level = (uu___210_15217.delta_level);
               primitive_steps = (uu___210_15217.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____15222 = norm1 t in
          FStar_Syntax_Util.non_informative uu____15222 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____15225 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___211_15244 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.pos =
                (uu___211_15244.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___211_15244.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____15251 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____15251
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
                    let uu___212_15262 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___212_15262.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___212_15262.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___212_15262.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___213_15264 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___213_15264.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___213_15264.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___213_15264.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___213_15264.FStar_Syntax_Syntax.flags)
                    } in
              let uu___214_15265 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos =
                  (uu___214_15265.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___214_15265.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____15267 -> c
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____15270  ->
        match uu____15270 with
        | (x,imp) ->
            let uu____15273 =
              let uu___215_15274 = x in
              let uu____15275 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___215_15274.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___215_15274.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____15275
              } in
            (uu____15273, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____15281 =
          FStar_List.fold_left
            (fun uu____15299  ->
               fun b  ->
                 match uu____15299 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____15281 with | (nbs,uu____15327) -> FStar_List.rev nbs
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
            let uu____15343 =
              let uu___216_15344 = rc in
              let uu____15345 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___216_15344.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____15345;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___216_15344.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____15343
        | uu____15352 -> lopt
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
              ((let uu____15365 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____15365
                then
                  let time_now = FStar_Util.now () in
                  let uu____15367 =
                    let uu____15368 =
                      let uu____15369 =
                        FStar_Util.time_diff time_then time_now in
                      FStar_Pervasives_Native.snd uu____15369 in
                    FStar_Util.string_of_int uu____15368 in
                  let uu____15374 = FStar_Syntax_Print.term_to_string tm in
                  let uu____15375 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                    uu____15367 uu____15374 uu____15375
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___217_15393 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___217_15393.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____15462  ->
                    let uu____15463 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____15463);
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
              let uu____15499 =
                let uu___218_15500 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___218_15500.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___218_15500.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____15499
          | (Arg (Univ uu____15501,uu____15502,uu____15503))::uu____15504 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____15507,uu____15508))::uu____15509 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____15525),aq,r))::stack2 ->
              (log cfg
                 (fun uu____15554  ->
                    let uu____15555 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____15555);
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
                 (let uu____15565 = FStar_ST.op_Bang m in
                  match uu____15565 with
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
                  | FStar_Pervasives_Native.Some (uu____15665,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq)
                          FStar_Pervasives_Native.None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 =
                FStar_Syntax_Syntax.extend_app head1 (t, aq)
                  FStar_Pervasives_Native.None r in
              let uu____15689 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____15689
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____15699  ->
                    let uu____15700 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____15700);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____15705 =
                  log cfg
                    (fun uu____15710  ->
                       let uu____15711 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____15712 =
                         let uu____15713 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____15730  ->
                                   match uu____15730 with
                                   | (p,uu____15740,uu____15741) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____15713
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____15711 uu____15712);
                  (let whnf = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___160_15758  ->
                               match uu___160_15758 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____15759 -> false)) in
                     let steps' =
                       let uu____15763 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____15763
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___219_15767 = cfg in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___219_15767.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___219_15767.primitive_steps)
                     } in
                   let norm_or_whnf env2 t1 =
                     if whnf
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____15811 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____15834 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____15900  ->
                                   fun uu____15901  ->
                                     match (uu____15900, uu____15901) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____16004 = norm_pat env3 p1 in
                                         (match uu____16004 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____15834 with
                          | (pats1,env3) ->
                              ((let uu___220_16106 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.p =
                                    (uu___220_16106.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___221_16125 = x in
                           let uu____16126 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___221_16125.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___221_16125.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16126
                           } in
                         ((let uu___222_16134 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.p =
                               (uu___222_16134.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___223_16139 = x in
                           let uu____16140 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___223_16139.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___223_16139.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16140
                           } in
                         ((let uu___224_16148 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.p =
                               (uu___224_16148.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___225_16158 = x in
                           let uu____16159 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___225_16158.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___225_16158.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16159
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___226_16168 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.p =
                               (uu___226_16168.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf -> branches
                     | uu____16172 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____16186 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____16186 with
                                 | (p,wopt,e) ->
                                     let uu____16206 = norm_pat env1 p in
                                     (match uu____16206 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Pervasives_Native.Some w
                                                ->
                                                let uu____16237 =
                                                  norm_or_whnf env2 w in
                                                FStar_Pervasives_Native.Some
                                                  uu____16237 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____16243 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____16243) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____16253) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____16258 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____16259;
                        FStar_Syntax_Syntax.fv_delta = uu____16260;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Data_ctor );_}
                      -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____16261;
                        FStar_Syntax_Syntax.fv_delta = uu____16262;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Record_ctor uu____16263);_}
                      -> true
                  | uu____16270 -> false in
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
                  let uu____16399 =
                    FStar_Syntax_Util.head_and_args scrutinee1 in
                  match uu____16399 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var uu____16448 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_wild uu____16451 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____16454 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee1.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____16473 ->
                                let uu____16474 =
                                  let uu____16475 = is_cons head1 in
                                  Prims.op_Negation uu____16475 in
                                FStar_Util.Inr uu____16474)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____16496 =
                             let uu____16497 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____16497.FStar_Syntax_Syntax.n in
                           (match uu____16496 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____16507 ->
                                let uu____16508 =
                                  let uu____16509 = is_cons head1 in
                                  Prims.op_Negation uu____16509 in
                                FStar_Util.Inr uu____16508))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____16562)::rest_a,(p1,uu____16565)::rest_p) ->
                      let uu____16609 = matches_pat t1 p1 in
                      (match uu____16609 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____16634 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____16736 = matches_pat scrutinee1 p1 in
                      (match uu____16736 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____16756  ->
                                 let uu____16757 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____16758 =
                                   let uu____16759 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____16759
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____16757 uu____16758);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____16776 =
                                        let uu____16777 =
                                          let uu____16796 =
                                            FStar_Util.mk_ref
                                              (FStar_Pervasives_Native.Some
                                                 ([], t1)) in
                                          ([], t1, uu____16796, false) in
                                        Clos uu____16777 in
                                      uu____16776 :: env2) env1 s in
                             let uu____16849 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____16849))) in
                let uu____16850 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____16850
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___161_16873  ->
                match uu___161_16873 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____16877 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____16883 -> d in
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
            let uu___227_16912 = config s e in
            {
              steps = (uu___227_16912.steps);
              tcenv = (uu___227_16912.tcenv);
              delta_level = (uu___227_16912.delta_level);
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
      fun t  -> let uu____16937 = config s e in norm_comp uu____16937 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____16946 = config [] env in norm_universe uu____16946 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let uu____16955 = config [] env in ghost_to_pure_aux uu____16955 [] c
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
        let uu____16969 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____16969 in
      let uu____16970 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____16970
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___228_16972 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___228_16972.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___228_16972.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____16975  ->
                    let uu____16976 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____16976))
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
            ((let uu____16995 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____16995);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____17008 = config [AllowUnboundUniverses] env in
          norm_comp uu____17008 [] c
        with
        | e ->
            ((let uu____17015 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____17015);
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
                   let uu____17055 =
                     let uu____17056 =
                       let uu____17063 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____17063) in
                     FStar_Syntax_Syntax.Tm_refine uu____17056 in
                   mk uu____17055 t01.FStar_Syntax_Syntax.pos
               | uu____17068 -> t2)
          | uu____17069 -> t2 in
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
        let uu____17121 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____17121 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____17150 ->
                 let uu____17157 = FStar_Syntax_Util.abs_formals e in
                 (match uu____17157 with
                  | (actuals,uu____17167,uu____17168) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____17182 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____17182 with
                         | (binders,args) ->
                             let uu____17199 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____17199
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
      | uu____17209 ->
          let uu____17210 = FStar_Syntax_Util.head_and_args t in
          (match uu____17210 with
           | (head1,args) ->
               let uu____17247 =
                 let uu____17248 = FStar_Syntax_Subst.compress head1 in
                 uu____17248.FStar_Syntax_Syntax.n in
               (match uu____17247 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____17251,thead) ->
                    let uu____17277 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____17277 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____17319 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___233_17327 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___233_17327.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___233_17327.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___233_17327.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___233_17327.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___233_17327.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___233_17327.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___233_17327.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___233_17327.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___233_17327.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___233_17327.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___233_17327.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___233_17327.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___233_17327.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___233_17327.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___233_17327.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___233_17327.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___233_17327.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___233_17327.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___233_17327.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___233_17327.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___233_17327.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___233_17327.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___233_17327.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___233_17327.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___233_17327.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___233_17327.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___233_17327.FStar_TypeChecker_Env.identifier_info)
                                 }) t in
                            match uu____17319 with
                            | (uu____17328,ty,uu____17330) ->
                                eta_expand_with_type env t ty))
                | uu____17331 ->
                    let uu____17332 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___234_17340 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___234_17340.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___234_17340.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___234_17340.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___234_17340.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___234_17340.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___234_17340.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___234_17340.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___234_17340.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___234_17340.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___234_17340.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___234_17340.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___234_17340.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___234_17340.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___234_17340.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___234_17340.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___234_17340.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___234_17340.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___234_17340.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___234_17340.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___234_17340.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.type_of =
                             (uu___234_17340.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___234_17340.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___234_17340.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___234_17340.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___234_17340.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___234_17340.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___234_17340.FStar_TypeChecker_Env.identifier_info)
                         }) t in
                    (match uu____17332 with
                     | (uu____17341,ty,uu____17343) ->
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
            | (uu____17421,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____17427,FStar_Util.Inl t) ->
                let uu____17433 =
                  let uu____17436 =
                    let uu____17437 =
                      let uu____17450 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____17450) in
                    FStar_Syntax_Syntax.Tm_arrow uu____17437 in
                  FStar_Syntax_Syntax.mk uu____17436 in
                uu____17433 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____17454 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____17454 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____17481 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____17536 ->
                    let uu____17537 =
                      let uu____17546 =
                        let uu____17547 = FStar_Syntax_Subst.compress t3 in
                        uu____17547.FStar_Syntax_Syntax.n in
                      (uu____17546, tc) in
                    (match uu____17537 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____17572) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____17609) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____17648,FStar_Util.Inl uu____17649) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____17672 -> failwith "Impossible") in
              (match uu____17481 with
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
          let uu____17781 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____17781 with
          | (univ_names1,binders1,tc) ->
              let uu____17839 = FStar_Util.left tc in
              (univ_names1, binders1, uu____17839)
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
          let uu____17878 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____17878 with
          | (univ_names1,binders1,tc) ->
              let uu____17938 = FStar_Util.right tc in
              (univ_names1, binders1, uu____17938)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____17973 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____17973 with
           | (univ_names1,binders1,typ1) ->
               let uu___235_18001 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___235_18001.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___235_18001.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___235_18001.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___235_18001.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___236_18022 = s in
          let uu____18023 =
            let uu____18024 =
              let uu____18033 = FStar_List.map (elim_uvars env) sigs in
              (uu____18033, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____18024 in
          {
            FStar_Syntax_Syntax.sigel = uu____18023;
            FStar_Syntax_Syntax.sigrng =
              (uu___236_18022.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___236_18022.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___236_18022.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___236_18022.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____18050 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____18050 with
           | (univ_names1,uu____18068,typ1) ->
               let uu___237_18082 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___237_18082.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___237_18082.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___237_18082.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___237_18082.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____18088 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____18088 with
           | (univ_names1,uu____18106,typ1) ->
               let uu___238_18120 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___238_18120.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___238_18120.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___238_18120.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___238_18120.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____18154 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____18154 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____18177 =
                            let uu____18178 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____18178 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____18177 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___239_18181 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___239_18181.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___239_18181.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___240_18182 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___240_18182.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___240_18182.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___240_18182.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___240_18182.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___241_18194 = s in
          let uu____18195 =
            let uu____18196 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____18196 in
          {
            FStar_Syntax_Syntax.sigel = uu____18195;
            FStar_Syntax_Syntax.sigrng =
              (uu___241_18194.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___241_18194.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___241_18194.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___241_18194.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____18200 = elim_uvars_aux_t env us [] t in
          (match uu____18200 with
           | (us1,uu____18218,t1) ->
               let uu___242_18232 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___242_18232.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___242_18232.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___242_18232.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___242_18232.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____18233 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____18235 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____18235 with
           | (univs1,binders,signature) ->
               let uu____18263 =
                 let uu____18272 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____18272 with
                 | (univs_opening,univs2) ->
                     let uu____18299 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____18299) in
               (match uu____18263 with
                | (univs_opening,univs_closing) ->
                    let uu____18316 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____18322 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____18323 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____18322, uu____18323) in
                    (match uu____18316 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____18345 =
                           match uu____18345 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____18363 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____18363 with
                                | (us1,t1) ->
                                    let uu____18374 =
                                      let uu____18379 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____18386 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____18379, uu____18386) in
                                    (match uu____18374 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____18399 =
                                           let uu____18404 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____18413 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____18404, uu____18413) in
                                         (match uu____18399 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____18429 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____18429 in
                                              let uu____18430 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____18430 with
                                               | (uu____18451,uu____18452,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____18467 =
                                                       let uu____18468 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____18468 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____18467 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____18473 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____18473 with
                           | (uu____18486,uu____18487,t1) -> t1 in
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
                             | uu____18547 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____18564 =
                               let uu____18565 =
                                 FStar_Syntax_Subst.compress body in
                               uu____18565.FStar_Syntax_Syntax.n in
                             match uu____18564 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____18624 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____18653 =
                               let uu____18654 =
                                 FStar_Syntax_Subst.compress t in
                               uu____18654.FStar_Syntax_Syntax.n in
                             match uu____18653 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____18675) ->
                                 let uu____18696 = destruct_action_body body in
                                 (match uu____18696 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____18741 ->
                                 let uu____18742 = destruct_action_body t in
                                 (match uu____18742 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____18791 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____18791 with
                           | (action_univs,t) ->
                               let uu____18800 = destruct_action_typ_templ t in
                               (match uu____18800 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___243_18841 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___243_18841.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___243_18841.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___244_18843 = ed in
                           let uu____18844 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____18845 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____18846 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____18847 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____18848 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____18849 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____18850 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____18851 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____18852 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____18853 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____18854 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____18855 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____18856 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____18857 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___244_18843.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___244_18843.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____18844;
                             FStar_Syntax_Syntax.bind_wp = uu____18845;
                             FStar_Syntax_Syntax.if_then_else = uu____18846;
                             FStar_Syntax_Syntax.ite_wp = uu____18847;
                             FStar_Syntax_Syntax.stronger = uu____18848;
                             FStar_Syntax_Syntax.close_wp = uu____18849;
                             FStar_Syntax_Syntax.assert_p = uu____18850;
                             FStar_Syntax_Syntax.assume_p = uu____18851;
                             FStar_Syntax_Syntax.null_wp = uu____18852;
                             FStar_Syntax_Syntax.trivial = uu____18853;
                             FStar_Syntax_Syntax.repr = uu____18854;
                             FStar_Syntax_Syntax.return_repr = uu____18855;
                             FStar_Syntax_Syntax.bind_repr = uu____18856;
                             FStar_Syntax_Syntax.actions = uu____18857
                           } in
                         let uu___245_18860 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___245_18860.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___245_18860.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___245_18860.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___245_18860.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___162_18877 =
            match uu___162_18877 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____18904 = elim_uvars_aux_t env us [] t in
                (match uu____18904 with
                 | (us1,uu____18928,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___246_18947 = sub_eff in
            let uu____18948 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____18951 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___246_18947.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___246_18947.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____18948;
              FStar_Syntax_Syntax.lift = uu____18951
            } in
          let uu___247_18954 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___247_18954.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___247_18954.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___247_18954.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___247_18954.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____18964 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____18964 with
           | (univ_names1,binders1,comp1) ->
               let uu___248_18998 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___248_18998.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___248_18998.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___248_18998.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___248_18998.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____19009 -> s