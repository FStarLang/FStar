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
  fun uu___145_390  ->
    match uu___145_390 with
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
  fun uu___147_1842  ->
    match uu___147_1842 with | [] -> true | uu____1845 -> false
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
                           (let uu___165_3019 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___165_3019.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___165_3019.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____3013)) in
                  (match uu____2983 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___166_3035 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___166_3035.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___166_3035.FStar_Syntax_Syntax.lbeff);
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
                           (let uu___167_3118 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___167_3118.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___167_3118.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_43  -> FStar_Util.Inl _0_43)) in
                    let uu___168_3119 = lb in
                    let uu____3120 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___168_3119.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___168_3119.FStar_Syntax_Syntax.lbeff);
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
                                   ((let uu___169_3577 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___169_3577.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___170_3596 = x in
                                let uu____3597 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___170_3596.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___170_3596.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3597
                                } in
                              ((let uu___171_3605 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___171_3605.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___172_3610 = x in
                                let uu____3611 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___172_3610.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___172_3610.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3611
                                } in
                              ((let uu___173_3619 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___173_3619.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___174_3629 = x in
                                let uu____3630 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___174_3629.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___174_3629.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3630
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___175_3639 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___175_3639.FStar_Syntax_Syntax.p)
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
                          let uu___176_4005 = b in
                          let uu____4006 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___176_4005.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___176_4005.FStar_Syntax_Syntax.index);
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
                        (fun uu___148_4143  ->
                           match uu___148_4143 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____4147 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____4147
                           | f -> f)) in
                 let uu____4151 =
                   let uu___177_4152 = c1 in
                   let uu____4153 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____4153;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___177_4152.FStar_Syntax_Syntax.effect_name);
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
         (fun uu___149_4163  ->
            match uu___149_4163 with
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
                   (fun uu___150_4187  ->
                      match uu___150_4187 with
                      | FStar_Syntax_Syntax.DECREASES uu____4188 -> false
                      | uu____4191 -> true)) in
            let rc1 =
              let uu___178_4193 = rc in
              let uu____4194 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___178_4193.FStar_Syntax_Syntax.residual_effect);
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
          (let uu___179_5315 = t in
           {
             FStar_Syntax_Syntax.n = (uu___179_5315.FStar_Syntax_Syntax.n);
             FStar_Syntax_Syntax.pos = r1;
             FStar_Syntax_Syntax.vars =
               (uu___179_5315.FStar_Syntax_Syntax.vars)
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
               (let uu___180_7149 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___180_7149.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___180_7149.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___181_7153 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___181_7153.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___181_7153.FStar_Syntax_Syntax.vars)
                })
         | uu____7154 -> FStar_Pervasives_Native.None)
    | (_typ,uu____7156)::uu____7157::(a1,uu____7159)::(a2,uu____7161)::[] ->
        let uu____7210 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____7210 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___180_7216 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___180_7216.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___180_7216.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___181_7220 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___181_7220.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___181_7220.FStar_Syntax_Syntax.vars)
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
        (let uu___182_7307 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___182_7307.tcenv);
           delta_level = (uu___182_7307.delta_level);
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
        let uu___183_7331 = t in
        {
          FStar_Syntax_Syntax.n = (uu___183_7331.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___183_7331.FStar_Syntax_Syntax.vars)
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
let get_norm_request:
  'Auu____10410 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10410) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let unembed_step s1 =
          let uu____10452 =
            let uu____10453 = FStar_Syntax_Util.un_uinst s1 in
            uu____10453.FStar_Syntax_Syntax.n in
          match uu____10452 with
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
                 FStar_Syntax_Syntax.pos = uu____10462;
                 FStar_Syntax_Syntax.vars = uu____10463;_},(names1,uu____10465)::[])
              when
              FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.steps_delta_only
              ->
              let names2 = FStar_Syntax_Embeddings.unembed_string_list names1 in
              let lids =
                FStar_All.pipe_right names2
                  (FStar_List.map FStar_Ident.lid_of_str) in
              UnfoldOnly lids
          | uu____10504 -> failwith "Not an embedded `Prims.step`" in
        FStar_Syntax_Embeddings.unembed_list unembed_step s in
      match args with
      | uu____10511::(tm,uu____10513)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____10536)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____10551)::uu____10552::(tm,uu____10554)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____10594 =
              let uu____10597 = full_norm steps in parse_steps uu____10597 in
            Beta :: uu____10594 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____10606 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___151_10624  ->
    match uu___151_10624 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.pos = uu____10627;
           FStar_Syntax_Syntax.vars = uu____10628;_},uu____10629,uu____10630))::uu____10631
        -> true
    | uu____10638 -> false
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
            (fun uu____10773  ->
               let uu____10774 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____10775 = FStar_Syntax_Print.term_to_string t1 in
               let uu____10776 =
                 let uu____10777 =
                   let uu____10780 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____10780 in
                 stack_to_string uu____10777 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____10774
                 uu____10775 uu____10776);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____10803 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____10828 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____10845 =
                 let uu____10846 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____10847 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____10846 uu____10847 in
               failwith uu____10845
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____10848 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____10865 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____10866 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10867;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____10868;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10871;
                 FStar_Syntax_Syntax.fv_delta = uu____10872;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10873;
                 FStar_Syntax_Syntax.fv_delta = uu____10874;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____10875);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (FStar_Syntax_Util.is_fstar_tactics_embed hd1) ||
                 (FStar_Syntax_Util.is_fstar_tactics_by_tactic hd1)
               ->
               let args1 = closures_as_args_delayed cfg env args in
               let hd2 = closure_as_term cfg env hd1 in
               let t2 =
                 let uu___184_10917 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___184_10917.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___184_10917.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____10950 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____10950) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___185_10958 = cfg in
                 let uu____10959 =
                   FStar_List.filter
                     (fun uu___152_10962  ->
                        match uu___152_10962 with
                        | UnfoldOnly uu____10963 -> false
                        | NoDeltaSteps  -> false
                        | uu____10966 -> true) cfg.steps in
                 {
                   steps = uu____10959;
                   tcenv = (uu___185_10958.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___185_10958.primitive_steps)
                 } in
               let uu____10967 = get_norm_request (norm cfg' env []) args in
               (match uu____10967 with
                | (s,tm) ->
                    let delta_level =
                      let uu____10983 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___153_10988  ->
                                match uu___153_10988 with
                                | UnfoldUntil uu____10989 -> true
                                | UnfoldOnly uu____10990 -> true
                                | uu____10993 -> false)) in
                      if uu____10983
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___186_10998 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___186_10998.tcenv);
                        delta_level;
                        primitive_steps = (uu___186_10998.primitive_steps)
                      } in
                    let stack' =
                      let tail1 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let uu____11009 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____11009
                      then
                        let uu____11012 =
                          let uu____11013 =
                            let uu____11018 = FStar_Util.now () in
                            (t1, uu____11018) in
                          Debug uu____11013 in
                        uu____11012 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11020;
                  FStar_Syntax_Syntax.vars = uu____11021;_},a1::a2::rest)
               ->
               let uu____11069 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11069 with
                | (hd1,uu____11085) ->
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
                    (FStar_Const.Const_reflect uu____11150);
                  FStar_Syntax_Syntax.pos = uu____11151;
                  FStar_Syntax_Syntax.vars = uu____11152;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____11184 = FStar_List.tl stack1 in
               norm cfg env uu____11184 (FStar_Pervasives_Native.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11187;
                  FStar_Syntax_Syntax.vars = uu____11188;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____11220 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11220 with
                | (reify_head,uu____11236) ->
                    let a1 =
                      let uu____11258 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (FStar_Pervasives_Native.fst a) in
                      FStar_Syntax_Subst.compress uu____11258 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____11261);
                            FStar_Syntax_Syntax.pos = uu____11262;
                            FStar_Syntax_Syntax.vars = uu____11263;_},a2::[])
                         ->
                         norm cfg env stack1 (FStar_Pervasives_Native.fst a2)
                     | uu____11297 ->
                         let stack2 =
                           (App
                              (reify_head, FStar_Pervasives_Native.None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11307 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____11307
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11314 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11314
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____11317 =
                      let uu____11324 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11324, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11317 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___154_11338  ->
                         match uu___154_11338 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11341 =
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
                 if uu____11341
                 then false
                 else
                   (let uu____11343 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___155_11350  ->
                              match uu___155_11350 with
                              | UnfoldOnly uu____11351 -> true
                              | uu____11354 -> false)) in
                    match uu____11343 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11358 -> should_delta) in
               if Prims.op_Negation should_delta1
               then rebuild cfg env stack1 t1
               else
                 (let r_env =
                    let uu____11363 = FStar_Syntax_Syntax.range_of_fv f in
                    FStar_TypeChecker_Env.set_range cfg.tcenv uu____11363 in
                  let uu____11364 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  match uu____11364 with
                  | FStar_Pervasives_Native.None  ->
                      (log cfg
                         (fun uu____11377  ->
                            FStar_Util.print "Tm_fvar case 2\n" []);
                       rebuild cfg env stack1 t1)
                  | FStar_Pervasives_Native.Some (us,t2) ->
                      (log cfg
                         (fun uu____11388  ->
                            let uu____11389 =
                              FStar_Syntax_Print.term_to_string t0 in
                            let uu____11390 =
                              FStar_Syntax_Print.term_to_string t2 in
                            FStar_Util.print2 ">>> Unfolded %s to %s\n"
                              uu____11389 uu____11390);
                       (let t3 =
                          let uu____11392 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 (UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant)) in
                          if uu____11392
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
                          | (UnivArgs (us',uu____11402))::stack2 ->
                              let env1 =
                                FStar_All.pipe_right us'
                                  (FStar_List.fold_left
                                     (fun env1  -> fun u  -> (Univ u) :: env1)
                                     env) in
                              norm cfg env1 stack2 t3
                          | uu____11425 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack1 t3
                          | uu____11426 ->
                              let uu____11427 =
                                let uu____11428 =
                                  FStar_Syntax_Print.lid_to_string
                                    (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                FStar_Util.format1
                                  "Impossible: missing universe instantiation on %s"
                                  uu____11428 in
                              failwith uu____11427
                        else norm cfg env stack1 t3)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11431 = lookup_bvar env x in
               (match uu____11431 with
                | Univ uu____11432 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11457 = FStar_ST.op_Bang r in
                      (match uu____11457 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11538  ->
                                 let uu____11539 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____11540 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11539
                                   uu____11540);
                            (let uu____11541 =
                               let uu____11542 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____11542.FStar_Syntax_Syntax.n in
                             match uu____11541 with
                             | FStar_Syntax_Syntax.Tm_abs uu____11545 ->
                                 norm cfg env2 stack1 t'
                             | uu____11562 -> rebuild cfg env2 stack1 t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____11614)::uu____11615 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11624)::uu____11625 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11635,uu____11636))::stack_rest ->
                    (match c with
                     | Univ uu____11640 -> norm cfg (c :: env) stack_rest t1
                     | uu____11641 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____11646::[] ->
                              (match lopt with
                               | FStar_Pervasives_Native.None  when
                                   FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____11662  ->
                                         let uu____11663 =
                                           closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____11663);
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
                                           (fun uu___156_11668  ->
                                              match uu___156_11668 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____11669 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____11673  ->
                                         let uu____11674 =
                                           closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____11674);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____11675 when
                                   (FStar_All.pipe_right cfg.steps
                                      (FStar_List.contains Reify))
                                     ||
                                     (FStar_All.pipe_right cfg.steps
                                        (FStar_List.contains CheckNoUvars))
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____11678 ->
                                   let cfg1 =
                                     let uu___187_11682 = cfg in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___187_11682.tcenv);
                                       delta_level =
                                         (uu___187_11682.delta_level);
                                       primitive_steps =
                                         (uu___187_11682.primitive_steps)
                                     } in
                                   let uu____11683 =
                                     closure_as_term cfg1 env t1 in
                                   rebuild cfg1 env stack1 uu____11683)
                          | uu____11684::tl1 ->
                              (log cfg
                                 (fun uu____11703  ->
                                    let uu____11704 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11704);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___188_11734 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___188_11734.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____11795  ->
                          let uu____11796 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11796);
                     norm cfg env stack2 t1)
                | (Debug uu____11797)::uu____11798 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11805 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11805
                    else
                      (let uu____11807 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11807 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11831  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11847 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11847
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11857 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11857)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___189_11862 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___189_11862.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___189_11862.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11863 -> lopt in
                           (log cfg
                              (fun uu____11869  ->
                                 let uu____11870 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11870);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___190_11883 = cfg in
                               let uu____11884 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___190_11883.steps);
                                 tcenv = (uu___190_11883.tcenv);
                                 delta_level = (uu___190_11883.delta_level);
                                 primitive_steps = uu____11884
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____11893)::uu____11894 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11901 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11901
                    else
                      (let uu____11903 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11903 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11927  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11943 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11943
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11953 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11953)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___189_11958 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___189_11958.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___189_11958.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11959 -> lopt in
                           (log cfg
                              (fun uu____11965  ->
                                 let uu____11966 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11966);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___190_11979 = cfg in
                               let uu____11980 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___190_11979.steps);
                                 tcenv = (uu___190_11979.tcenv);
                                 delta_level = (uu___190_11979.delta_level);
                                 primitive_steps = uu____11980
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____11989)::uu____11990 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12001 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12001
                    else
                      (let uu____12003 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12003 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12027  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12043 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12043
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12053 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12053)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___189_12058 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___189_12058.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___189_12058.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12059 -> lopt in
                           (log cfg
                              (fun uu____12065  ->
                                 let uu____12066 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12066);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___190_12079 = cfg in
                               let uu____12080 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___190_12079.steps);
                                 tcenv = (uu___190_12079.tcenv);
                                 delta_level = (uu___190_12079.delta_level);
                                 primitive_steps = uu____12080
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____12089)::uu____12090 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12099 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12099
                    else
                      (let uu____12101 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12101 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12125  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12141 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12141
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12151 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12151)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___189_12156 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___189_12156.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___189_12156.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12157 -> lopt in
                           (log cfg
                              (fun uu____12163  ->
                                 let uu____12164 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12164);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___190_12177 = cfg in
                               let uu____12178 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___190_12177.steps);
                                 tcenv = (uu___190_12177.tcenv);
                                 delta_level = (uu___190_12177.delta_level);
                                 primitive_steps = uu____12178
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____12187)::uu____12188 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12203 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12203
                    else
                      (let uu____12205 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12205 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12229  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12245 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12245
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12255 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12255)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___189_12260 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___189_12260.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___189_12260.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12261 -> lopt in
                           (log cfg
                              (fun uu____12267  ->
                                 let uu____12268 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12268);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___190_12281 = cfg in
                               let uu____12282 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___190_12281.steps);
                                 tcenv = (uu___190_12281.tcenv);
                                 delta_level = (uu___190_12281.delta_level);
                                 primitive_steps = uu____12282
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12291 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12291
                    else
                      (let uu____12293 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12293 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12317  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12333 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12333
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12343 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12343)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___189_12348 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___189_12348.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___189_12348.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12349 -> lopt in
                           (log cfg
                              (fun uu____12355  ->
                                 let uu____12356 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12356);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___190_12369 = cfg in
                               let uu____12370 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___190_12369.steps);
                                 tcenv = (uu___190_12369.tcenv);
                                 delta_level = (uu___190_12369.delta_level);
                                 primitive_steps = uu____12370
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
                      (fun uu____12417  ->
                         fun stack2  ->
                           match uu____12417 with
                           | (a,aq) ->
                               let uu____12429 =
                                 let uu____12430 =
                                   let uu____12437 =
                                     let uu____12438 =
                                       let uu____12457 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____12457, false) in
                                     Clos uu____12438 in
                                   (uu____12437, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____12430 in
                               uu____12429 :: stack2) args) in
               (log cfg
                  (fun uu____12509  ->
                     let uu____12510 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12510);
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
                             ((let uu___191_12534 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___191_12534.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___191_12534.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____12535 ->
                      let uu____12540 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12540)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____12543 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____12543 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____12568 =
                          let uu____12569 =
                            let uu____12576 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___192_12578 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___192_12578.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___192_12578.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12576) in
                          FStar_Syntax_Syntax.Tm_refine uu____12569 in
                        mk uu____12568 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____12597 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____12597
               else
                 (let uu____12599 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____12599 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12607 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12619  -> Dummy :: env1) env) in
                        norm_comp cfg uu____12607 c1 in
                      let t2 =
                        let uu____12629 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____12629 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____12688)::uu____12689 -> norm cfg env stack1 t11
                | (Arg uu____12698)::uu____12699 -> norm cfg env stack1 t11
                | (App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____12708;
                       FStar_Syntax_Syntax.vars = uu____12709;_},uu____12710,uu____12711))::uu____12712
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____12719)::uu____12720 ->
                    norm cfg env stack1 t11
                | uu____12729 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____12733  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____12750 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____12750
                        | FStar_Util.Inr c ->
                            let uu____12758 = norm_comp cfg env c in
                            FStar_Util.Inr uu____12758 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____12764 =
                        let uu____12765 =
                          let uu____12766 =
                            let uu____12793 = FStar_Syntax_Util.unascribe t12 in
                            (uu____12793, (tc1, tacopt1), l) in
                          FStar_Syntax_Syntax.Tm_ascribed uu____12766 in
                        mk uu____12765 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____12764)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____12869,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____12870;
                               FStar_Syntax_Syntax.lbunivs = uu____12871;
                               FStar_Syntax_Syntax.lbtyp = uu____12872;
                               FStar_Syntax_Syntax.lbeff = uu____12873;
                               FStar_Syntax_Syntax.lbdef = uu____12874;_}::uu____12875),uu____12876)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____12912 =
                 (let uu____12915 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____12915) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____12917 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____12917))) in
               if uu____12912
               then
                 let env1 =
                   let uu____12921 =
                     let uu____12922 =
                       let uu____12941 =
                         FStar_Util.mk_ref FStar_Pervasives_Native.None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____12941,
                         false) in
                     Clos uu____12922 in
                   uu____12921 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____12993 =
                    let uu____12998 =
                      let uu____12999 =
                        let uu____13000 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____13000
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____12999] in
                    FStar_Syntax_Subst.open_term uu____12998 body in
                  match uu____12993 with
                  | (bs,body1) ->
                      let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                      let lbname =
                        let x =
                          let uu____13014 = FStar_List.hd bs in
                          FStar_Pervasives_Native.fst uu____13014 in
                        FStar_Util.Inl
                          (let uu___193_13024 = x in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___193_13024.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___193_13024.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = ty
                           }) in
                      let lb1 =
                        let uu___194_13026 = lb in
                        let uu____13027 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = lbname;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___194_13026.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = ty;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___194_13026.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____13027
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____13044  -> Dummy :: env1)
                             env) in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let ((true ,lbs),body) when
               FStar_List.contains CompressUvars cfg.steps ->
               let uu____13067 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____13067 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____13103 =
                               let uu___195_13104 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___195_13104.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___195_13104.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____13103 in
                           let uu____13105 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____13105 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____13125 =
                                   FStar_List.map (fun uu____13129  -> Dummy)
                                     lbs1 in
                                 let uu____13130 =
                                   let uu____13133 =
                                     FStar_List.map
                                       (fun uu____13141  -> Dummy) xs1 in
                                   FStar_List.append uu____13133 env in
                                 FStar_List.append uu____13125 uu____13130 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13153 =
                                       let uu___196_13154 = rc in
                                       let uu____13155 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___196_13154.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13155;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___196_13154.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____13153
                                 | uu____13162 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___197_13166 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___197_13166.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___197_13166.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____13170 =
                        FStar_List.map (fun uu____13174  -> Dummy) lbs2 in
                      FStar_List.append uu____13170 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____13176 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____13176 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___198_13192 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___198_13192.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___198_13192.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____13219 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____13219
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13238 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13289  ->
                        match uu____13289 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____13362 =
                                let uu___199_13363 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___199_13363.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___199_13363.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____13362 in
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
               (match uu____13238 with
                | (rec_env,memos,uu____13491) ->
                    let uu____13520 =
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
                             let uu____13925 =
                               let uu____13926 =
                                 let uu____13945 =
                                   FStar_Util.mk_ref
                                     FStar_Pervasives_Native.None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____13945, false) in
                               Clos uu____13926 in
                             uu____13925 :: env1)
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
                             FStar_Syntax_Syntax.pos = uu____14013;
                             FStar_Syntax_Syntax.vars = uu____14014;_},uu____14015,uu____14016))::uu____14017
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____14024 -> false in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____14034 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____14034
                        then
                          let uu___200_14035 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___200_14035.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps =
                              (uu___200_14035.primitive_steps)
                          }
                        else
                          (let uu___201_14037 = cfg in
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___201_14037.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta];
                             primitive_steps =
                               (uu___201_14037.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____14039 =
                         let uu____14040 = FStar_Syntax_Subst.compress head1 in
                         uu____14040.FStar_Syntax_Syntax.n in
                       match uu____14039 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____14058 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____14058 with
                            | (uu____14059,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____14065 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____14073 =
                                         let uu____14074 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____14074.FStar_Syntax_Syntax.n in
                                       match uu____14073 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____14080,uu____14081))
                                           ->
                                           let uu____14090 =
                                             let uu____14091 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____14091.FStar_Syntax_Syntax.n in
                                           (match uu____14090 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____14097,msrc,uu____14099))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____14108 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14108
                                            | uu____14109 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____14110 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____14111 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____14111 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___202_14116 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___202_14116.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___202_14116.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___202_14116.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____14117 =
                                            FStar_List.tl stack1 in
                                          let uu____14118 =
                                            let uu____14119 =
                                              let uu____14122 =
                                                let uu____14123 =
                                                  let uu____14136 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____14136) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____14123 in
                                              FStar_Syntax_Syntax.mk
                                                uu____14122 in
                                            uu____14119
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____14117
                                            uu____14118
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____14152 =
                                            let uu____14153 = is_return body in
                                            match uu____14153 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____14157;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____14158;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____14163 -> false in
                                          if uu____14152
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
                                               let uu____14187 =
                                                 let uu____14190 =
                                                   let uu____14191 =
                                                     let uu____14208 =
                                                       let uu____14211 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____14211] in
                                                     (uu____14208, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc)) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____14191 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____14190 in
                                               uu____14187
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____14227 =
                                                 let uu____14228 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____14228.FStar_Syntax_Syntax.n in
                                               match uu____14227 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____14234::uu____14235::[])
                                                   ->
                                                   let uu____14242 =
                                                     let uu____14245 =
                                                       let uu____14246 =
                                                         let uu____14253 =
                                                           let uu____14256 =
                                                             let uu____14257
                                                               =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____14257 in
                                                           let uu____14258 =
                                                             let uu____14261
                                                               =
                                                               let uu____14262
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____14262 in
                                                             [uu____14261] in
                                                           uu____14256 ::
                                                             uu____14258 in
                                                         (bind1, uu____14253) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____14246 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____14245 in
                                                   uu____14242
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____14270 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____14276 =
                                                 let uu____14279 =
                                                   let uu____14280 =
                                                     let uu____14295 =
                                                       let uu____14298 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____14299 =
                                                         let uu____14302 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____14303 =
                                                           let uu____14306 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____14307 =
                                                             let uu____14310
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____14311
                                                               =
                                                               let uu____14314
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____14315
                                                                 =
                                                                 let uu____14318
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____14318] in
                                                               uu____14314 ::
                                                                 uu____14315 in
                                                             uu____14310 ::
                                                               uu____14311 in
                                                           uu____14306 ::
                                                             uu____14307 in
                                                         uu____14302 ::
                                                           uu____14303 in
                                                       uu____14298 ::
                                                         uu____14299 in
                                                     (bind_inst, uu____14295) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____14280 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____14279 in
                                               uu____14276
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____14326 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____14326 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____14350 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____14350 with
                            | (uu____14351,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____14380 =
                                        let uu____14381 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____14381.FStar_Syntax_Syntax.n in
                                      match uu____14380 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____14387) -> t4
                                      | uu____14392 -> head2 in
                                    let uu____14393 =
                                      let uu____14394 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____14394.FStar_Syntax_Syntax.n in
                                    match uu____14393 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____14400 ->
                                        FStar_Pervasives_Native.None in
                                  let uu____14401 = maybe_extract_fv head2 in
                                  match uu____14401 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____14411 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____14411
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____14416 =
                                          maybe_extract_fv head3 in
                                        match uu____14416 with
                                        | FStar_Pervasives_Native.Some
                                            uu____14421 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____14422 ->
                                            FStar_Pervasives_Native.Some
                                              false in
                                      (head3, action_unfolded)
                                  | uu____14427 ->
                                      (head2, FStar_Pervasives_Native.None) in
                                ((let is_arg_impure uu____14442 =
                                    match uu____14442 with
                                    | (e,q) ->
                                        let uu____14449 =
                                          let uu____14450 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____14450.FStar_Syntax_Syntax.n in
                                        (match uu____14449 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____14465 -> false) in
                                  let uu____14466 =
                                    let uu____14467 =
                                      let uu____14474 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____14474 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____14467 in
                                  if uu____14466
                                  then
                                    let uu____14479 =
                                      let uu____14480 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____14480 in
                                    failwith uu____14479
                                  else ());
                                 (let uu____14482 =
                                    maybe_unfold_action head_app in
                                  match uu____14482 with
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
                                      let uu____14521 = FStar_List.tl stack1 in
                                      norm cfg env uu____14521 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____14535 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____14535 in
                           let uu____14536 = FStar_List.tl stack1 in
                           norm cfg env uu____14536 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____14657  ->
                                     match uu____14657 with
                                     | (pat,wopt,tm) ->
                                         let uu____14705 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____14705))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____14737 = FStar_List.tl stack1 in
                           norm cfg env uu____14737 tm
                       | uu____14738 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.pos = uu____14747;
                             FStar_Syntax_Syntax.vars = uu____14748;_},uu____14749,uu____14750))::uu____14751
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____14758 -> false in
                    if should_reify
                    then
                      let uu____14759 = FStar_List.tl stack1 in
                      let uu____14760 =
                        let uu____14761 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____14761 in
                      norm cfg env uu____14759 uu____14760
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____14764 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____14764
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___203_14773 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___203_14773.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___203_14773.primitive_steps)
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
                | uu____14775 ->
                    (match stack1 with
                     | uu____14776::uu____14777 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled
                              (l,r,uu____14782) ->
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
                          | uu____14807 -> norm cfg env stack1 head1)
                     | [] ->
                         let head2 = norm cfg env [] head1 in
                         let m1 =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               let uu____14821 =
                                 norm_pattern_args cfg env args in
                               FStar_Syntax_Syntax.Meta_pattern uu____14821
                           | uu____14832 -> m in
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
              let uu____14844 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____14844 with
              | (uu____14845,return_repr) ->
                  let return_inst =
                    let uu____14854 =
                      let uu____14855 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____14855.FStar_Syntax_Syntax.n in
                    match uu____14854 with
                    | FStar_Syntax_Syntax.Tm_uinst
                        (return_tm,uu____14861::[]) ->
                        let uu____14868 =
                          let uu____14871 =
                            let uu____14872 =
                              let uu____14879 =
                                let uu____14882 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____14882] in
                              (return_tm, uu____14879) in
                            FStar_Syntax_Syntax.Tm_uinst uu____14872 in
                          FStar_Syntax_Syntax.mk uu____14871 in
                        uu____14868 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____14890 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____14893 =
                    let uu____14896 =
                      let uu____14897 =
                        let uu____14912 =
                          let uu____14915 = FStar_Syntax_Syntax.as_arg t in
                          let uu____14916 =
                            let uu____14919 = FStar_Syntax_Syntax.as_arg e in
                            [uu____14919] in
                          uu____14915 :: uu____14916 in
                        (return_inst, uu____14912) in
                      FStar_Syntax_Syntax.Tm_app uu____14897 in
                    FStar_Syntax_Syntax.mk uu____14896 in
                  uu____14893 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____14928 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____14928 with
               | FStar_Pervasives_Native.None  ->
                   let uu____14931 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____14931
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____14932;
                     FStar_TypeChecker_Env.mtarget = uu____14933;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____14934;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____14945;
                     FStar_TypeChecker_Env.mtarget = uu____14946;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____14947;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____14965 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____14965)
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
                (fun uu____15021  ->
                   match uu____15021 with
                   | (a,imp) ->
                       let uu____15032 = norm cfg env [] a in
                       (uu____15032, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___204_15049 = comp1 in
            let uu____15052 =
              let uu____15053 =
                let uu____15062 = norm cfg env [] t in
                let uu____15063 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____15062, uu____15063) in
              FStar_Syntax_Syntax.Total uu____15053 in
            {
              FStar_Syntax_Syntax.n = uu____15052;
              FStar_Syntax_Syntax.pos =
                (uu___204_15049.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___204_15049.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___205_15078 = comp1 in
            let uu____15081 =
              let uu____15082 =
                let uu____15091 = norm cfg env [] t in
                let uu____15092 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____15091, uu____15092) in
              FStar_Syntax_Syntax.GTotal uu____15082 in
            {
              FStar_Syntax_Syntax.n = uu____15081;
              FStar_Syntax_Syntax.pos =
                (uu___205_15078.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___205_15078.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____15144  ->
                      match uu____15144 with
                      | (a,i) ->
                          let uu____15155 = norm cfg env [] a in
                          (uu____15155, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___157_15166  ->
                      match uu___157_15166 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____15170 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____15170
                      | f -> f)) in
            let uu___206_15174 = comp1 in
            let uu____15177 =
              let uu____15178 =
                let uu___207_15179 = ct in
                let uu____15180 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____15181 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____15184 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____15180;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___207_15179.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____15181;
                  FStar_Syntax_Syntax.effect_args = uu____15184;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____15178 in
            {
              FStar_Syntax_Syntax.n = uu____15177;
              FStar_Syntax_Syntax.pos =
                (uu___206_15174.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___206_15174.FStar_Syntax_Syntax.vars)
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
            (let uu___208_15202 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___208_15202.tcenv);
               delta_level = (uu___208_15202.delta_level);
               primitive_steps = (uu___208_15202.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____15207 = norm1 t in
          FStar_Syntax_Util.non_informative uu____15207 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____15210 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___209_15229 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.pos =
                (uu___209_15229.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___209_15229.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____15236 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____15236
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
                    let uu___210_15247 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___210_15247.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___210_15247.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___210_15247.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___211_15249 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___211_15249.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___211_15249.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___211_15249.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___211_15249.FStar_Syntax_Syntax.flags)
                    } in
              let uu___212_15250 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos =
                  (uu___212_15250.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___212_15250.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____15252 -> c
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____15255  ->
        match uu____15255 with
        | (x,imp) ->
            let uu____15258 =
              let uu___213_15259 = x in
              let uu____15260 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___213_15259.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___213_15259.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____15260
              } in
            (uu____15258, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____15266 =
          FStar_List.fold_left
            (fun uu____15284  ->
               fun b  ->
                 match uu____15284 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____15266 with | (nbs,uu____15312) -> FStar_List.rev nbs
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
            let uu____15328 =
              let uu___214_15329 = rc in
              let uu____15330 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___214_15329.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____15330;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___214_15329.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____15328
        | uu____15337 -> lopt
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
              ((let uu____15350 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____15350
                then
                  let time_now = FStar_Util.now () in
                  let uu____15352 =
                    let uu____15353 =
                      let uu____15354 =
                        FStar_Util.time_diff time_then time_now in
                      FStar_Pervasives_Native.snd uu____15354 in
                    FStar_Util.string_of_int uu____15353 in
                  let uu____15359 = FStar_Syntax_Print.term_to_string tm in
                  let uu____15360 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                    uu____15352 uu____15359 uu____15360
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___215_15378 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___215_15378.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____15447  ->
                    let uu____15448 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____15448);
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
              let uu____15484 =
                let uu___216_15485 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___216_15485.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___216_15485.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____15484
          | (Arg (Univ uu____15486,uu____15487,uu____15488))::uu____15489 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____15492,uu____15493))::uu____15494 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____15510),aq,r))::stack2 ->
              (log cfg
                 (fun uu____15539  ->
                    let uu____15540 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____15540);
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
                 (let uu____15550 = FStar_ST.op_Bang m in
                  match uu____15550 with
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
                  | FStar_Pervasives_Native.Some (uu____15650,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq)
                          FStar_Pervasives_Native.None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 =
                FStar_Syntax_Syntax.extend_app head1 (t, aq)
                  FStar_Pervasives_Native.None r in
              let uu____15674 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____15674
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____15684  ->
                    let uu____15685 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____15685);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____15690 =
                  log cfg
                    (fun uu____15695  ->
                       let uu____15696 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____15697 =
                         let uu____15698 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____15715  ->
                                   match uu____15715 with
                                   | (p,uu____15725,uu____15726) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____15698
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____15696 uu____15697);
                  (let whnf = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___158_15743  ->
                               match uu___158_15743 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____15744 -> false)) in
                     let steps' =
                       let uu____15748 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____15748
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___217_15752 = cfg in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___217_15752.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___217_15752.primitive_steps)
                     } in
                   let norm_or_whnf env2 t1 =
                     if whnf
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____15796 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____15819 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____15885  ->
                                   fun uu____15886  ->
                                     match (uu____15885, uu____15886) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____15989 = norm_pat env3 p1 in
                                         (match uu____15989 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____15819 with
                          | (pats1,env3) ->
                              ((let uu___218_16091 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.p =
                                    (uu___218_16091.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___219_16110 = x in
                           let uu____16111 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___219_16110.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___219_16110.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16111
                           } in
                         ((let uu___220_16119 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.p =
                               (uu___220_16119.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___221_16124 = x in
                           let uu____16125 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___221_16124.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___221_16124.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16125
                           } in
                         ((let uu___222_16133 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.p =
                               (uu___222_16133.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___223_16143 = x in
                           let uu____16144 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___223_16143.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___223_16143.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16144
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___224_16153 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.p =
                               (uu___224_16153.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf -> branches
                     | uu____16157 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____16171 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____16171 with
                                 | (p,wopt,e) ->
                                     let uu____16191 = norm_pat env1 p in
                                     (match uu____16191 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Pervasives_Native.Some w
                                                ->
                                                let uu____16222 =
                                                  norm_or_whnf env2 w in
                                                FStar_Pervasives_Native.Some
                                                  uu____16222 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____16228 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____16228) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____16238) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____16243 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____16244;
                        FStar_Syntax_Syntax.fv_delta = uu____16245;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Data_ctor );_}
                      -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____16246;
                        FStar_Syntax_Syntax.fv_delta = uu____16247;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Record_ctor uu____16248);_}
                      -> true
                  | uu____16255 -> false in
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
                  let uu____16384 =
                    FStar_Syntax_Util.head_and_args scrutinee1 in
                  match uu____16384 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var uu____16433 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_wild uu____16436 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____16439 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee1.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____16458 ->
                                let uu____16459 =
                                  let uu____16460 = is_cons head1 in
                                  Prims.op_Negation uu____16460 in
                                FStar_Util.Inr uu____16459)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____16481 =
                             let uu____16482 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____16482.FStar_Syntax_Syntax.n in
                           (match uu____16481 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____16492 ->
                                let uu____16493 =
                                  let uu____16494 = is_cons head1 in
                                  Prims.op_Negation uu____16494 in
                                FStar_Util.Inr uu____16493))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____16547)::rest_a,(p1,uu____16550)::rest_p) ->
                      let uu____16594 = matches_pat t1 p1 in
                      (match uu____16594 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____16619 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____16721 = matches_pat scrutinee1 p1 in
                      (match uu____16721 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____16741  ->
                                 let uu____16742 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____16743 =
                                   let uu____16744 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____16744
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____16742 uu____16743);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____16761 =
                                        let uu____16762 =
                                          let uu____16781 =
                                            FStar_Util.mk_ref
                                              (FStar_Pervasives_Native.Some
                                                 ([], t1)) in
                                          ([], t1, uu____16781, false) in
                                        Clos uu____16762 in
                                      uu____16761 :: env2) env1 s in
                             let uu____16834 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____16834))) in
                let uu____16835 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____16835
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___159_16858  ->
                match uu___159_16858 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____16862 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____16868 -> d in
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
            let uu___225_16897 = config s e in
            {
              steps = (uu___225_16897.steps);
              tcenv = (uu___225_16897.tcenv);
              delta_level = (uu___225_16897.delta_level);
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
      fun t  -> let uu____16922 = config s e in norm_comp uu____16922 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____16931 = config [] env in norm_universe uu____16931 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let uu____16940 = config [] env in ghost_to_pure_aux uu____16940 [] c
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
        let uu____16954 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____16954 in
      let uu____16955 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____16955
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___226_16957 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___226_16957.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___226_16957.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____16960  ->
                    let uu____16961 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____16961))
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
            ((let uu____16980 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____16980);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____16993 = config [AllowUnboundUniverses] env in
          norm_comp uu____16993 [] c
        with
        | e ->
            ((let uu____17000 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____17000);
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
                   let uu____17040 =
                     let uu____17041 =
                       let uu____17048 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____17048) in
                     FStar_Syntax_Syntax.Tm_refine uu____17041 in
                   mk uu____17040 t01.FStar_Syntax_Syntax.pos
               | uu____17053 -> t2)
          | uu____17054 -> t2 in
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
        let uu____17106 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____17106 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____17135 ->
                 let uu____17142 = FStar_Syntax_Util.abs_formals e in
                 (match uu____17142 with
                  | (actuals,uu____17152,uu____17153) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____17167 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____17167 with
                         | (binders,args) ->
                             let uu____17184 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____17184
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
      | uu____17194 ->
          let uu____17195 = FStar_Syntax_Util.head_and_args t in
          (match uu____17195 with
           | (head1,args) ->
               let uu____17232 =
                 let uu____17233 = FStar_Syntax_Subst.compress head1 in
                 uu____17233.FStar_Syntax_Syntax.n in
               (match uu____17232 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____17236,thead) ->
                    let uu____17262 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____17262 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____17304 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___231_17312 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___231_17312.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___231_17312.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___231_17312.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___231_17312.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___231_17312.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___231_17312.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___231_17312.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___231_17312.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___231_17312.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___231_17312.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___231_17312.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___231_17312.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___231_17312.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___231_17312.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___231_17312.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___231_17312.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___231_17312.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___231_17312.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___231_17312.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___231_17312.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___231_17312.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___231_17312.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___231_17312.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___231_17312.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___231_17312.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___231_17312.FStar_TypeChecker_Env.identifier_info)
                                 }) t in
                            match uu____17304 with
                            | (uu____17313,ty,uu____17315) ->
                                eta_expand_with_type env t ty))
                | uu____17316 ->
                    let uu____17317 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___232_17325 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___232_17325.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___232_17325.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___232_17325.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___232_17325.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___232_17325.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___232_17325.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___232_17325.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___232_17325.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___232_17325.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___232_17325.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___232_17325.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___232_17325.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___232_17325.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___232_17325.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___232_17325.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___232_17325.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___232_17325.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___232_17325.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___232_17325.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.type_of =
                             (uu___232_17325.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___232_17325.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___232_17325.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___232_17325.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___232_17325.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___232_17325.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___232_17325.FStar_TypeChecker_Env.identifier_info)
                         }) t in
                    (match uu____17317 with
                     | (uu____17326,ty,uu____17328) ->
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
            | (uu____17406,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____17412,FStar_Util.Inl t) ->
                let uu____17418 =
                  let uu____17421 =
                    let uu____17422 =
                      let uu____17435 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____17435) in
                    FStar_Syntax_Syntax.Tm_arrow uu____17422 in
                  FStar_Syntax_Syntax.mk uu____17421 in
                uu____17418 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____17439 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____17439 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____17466 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____17521 ->
                    let uu____17522 =
                      let uu____17531 =
                        let uu____17532 = FStar_Syntax_Subst.compress t3 in
                        uu____17532.FStar_Syntax_Syntax.n in
                      (uu____17531, tc) in
                    (match uu____17522 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____17557) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____17594) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____17633,FStar_Util.Inl uu____17634) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____17657 -> failwith "Impossible") in
              (match uu____17466 with
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
          let uu____17766 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____17766 with
          | (univ_names1,binders1,tc) ->
              let uu____17824 = FStar_Util.left tc in
              (univ_names1, binders1, uu____17824)
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
          let uu____17863 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____17863 with
          | (univ_names1,binders1,tc) ->
              let uu____17923 = FStar_Util.right tc in
              (univ_names1, binders1, uu____17923)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____17958 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____17958 with
           | (univ_names1,binders1,typ1) ->
               let uu___233_17986 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___233_17986.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___233_17986.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___233_17986.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___233_17986.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___234_18007 = s in
          let uu____18008 =
            let uu____18009 =
              let uu____18018 = FStar_List.map (elim_uvars env) sigs in
              (uu____18018, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____18009 in
          {
            FStar_Syntax_Syntax.sigel = uu____18008;
            FStar_Syntax_Syntax.sigrng =
              (uu___234_18007.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___234_18007.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___234_18007.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___234_18007.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____18035 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____18035 with
           | (univ_names1,uu____18053,typ1) ->
               let uu___235_18067 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___235_18067.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___235_18067.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___235_18067.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___235_18067.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____18073 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____18073 with
           | (univ_names1,uu____18091,typ1) ->
               let uu___236_18105 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___236_18105.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___236_18105.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___236_18105.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___236_18105.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____18139 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____18139 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____18162 =
                            let uu____18163 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____18163 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____18162 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___237_18166 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___237_18166.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___237_18166.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___238_18167 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___238_18167.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___238_18167.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___238_18167.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___238_18167.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___239_18179 = s in
          let uu____18180 =
            let uu____18181 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____18181 in
          {
            FStar_Syntax_Syntax.sigel = uu____18180;
            FStar_Syntax_Syntax.sigrng =
              (uu___239_18179.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___239_18179.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___239_18179.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___239_18179.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____18185 = elim_uvars_aux_t env us [] t in
          (match uu____18185 with
           | (us1,uu____18203,t1) ->
               let uu___240_18217 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___240_18217.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___240_18217.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___240_18217.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___240_18217.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____18218 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____18220 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____18220 with
           | (univs1,binders,signature) ->
               let uu____18248 =
                 let uu____18257 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____18257 with
                 | (univs_opening,univs2) ->
                     let uu____18284 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____18284) in
               (match uu____18248 with
                | (univs_opening,univs_closing) ->
                    let uu____18301 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____18307 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____18308 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____18307, uu____18308) in
                    (match uu____18301 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____18330 =
                           match uu____18330 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____18348 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____18348 with
                                | (us1,t1) ->
                                    let uu____18359 =
                                      let uu____18364 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____18371 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____18364, uu____18371) in
                                    (match uu____18359 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____18384 =
                                           let uu____18389 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____18398 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____18389, uu____18398) in
                                         (match uu____18384 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____18414 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____18414 in
                                              let uu____18415 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____18415 with
                                               | (uu____18436,uu____18437,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____18452 =
                                                       let uu____18453 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____18453 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____18452 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____18458 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____18458 with
                           | (uu____18471,uu____18472,t1) -> t1 in
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
                             | uu____18532 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____18549 =
                               let uu____18550 =
                                 FStar_Syntax_Subst.compress body in
                               uu____18550.FStar_Syntax_Syntax.n in
                             match uu____18549 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____18609 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____18638 =
                               let uu____18639 =
                                 FStar_Syntax_Subst.compress t in
                               uu____18639.FStar_Syntax_Syntax.n in
                             match uu____18638 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____18660) ->
                                 let uu____18681 = destruct_action_body body in
                                 (match uu____18681 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____18726 ->
                                 let uu____18727 = destruct_action_body t in
                                 (match uu____18727 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____18776 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____18776 with
                           | (action_univs,t) ->
                               let uu____18785 = destruct_action_typ_templ t in
                               (match uu____18785 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___241_18826 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___241_18826.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___241_18826.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___242_18828 = ed in
                           let uu____18829 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____18830 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____18831 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____18832 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____18833 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____18834 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____18835 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____18836 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____18837 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____18838 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____18839 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____18840 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____18841 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____18842 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___242_18828.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___242_18828.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____18829;
                             FStar_Syntax_Syntax.bind_wp = uu____18830;
                             FStar_Syntax_Syntax.if_then_else = uu____18831;
                             FStar_Syntax_Syntax.ite_wp = uu____18832;
                             FStar_Syntax_Syntax.stronger = uu____18833;
                             FStar_Syntax_Syntax.close_wp = uu____18834;
                             FStar_Syntax_Syntax.assert_p = uu____18835;
                             FStar_Syntax_Syntax.assume_p = uu____18836;
                             FStar_Syntax_Syntax.null_wp = uu____18837;
                             FStar_Syntax_Syntax.trivial = uu____18838;
                             FStar_Syntax_Syntax.repr = uu____18839;
                             FStar_Syntax_Syntax.return_repr = uu____18840;
                             FStar_Syntax_Syntax.bind_repr = uu____18841;
                             FStar_Syntax_Syntax.actions = uu____18842
                           } in
                         let uu___243_18845 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___243_18845.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___243_18845.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___243_18845.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___243_18845.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___160_18862 =
            match uu___160_18862 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____18889 = elim_uvars_aux_t env us [] t in
                (match uu____18889 with
                 | (us1,uu____18913,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___244_18932 = sub_eff in
            let uu____18933 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____18936 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___244_18932.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___244_18932.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____18933;
              FStar_Syntax_Syntax.lift = uu____18936
            } in
          let uu___245_18939 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___245_18939.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___245_18939.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___245_18939.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___245_18939.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____18949 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____18949 with
           | (univ_names1,binders1,comp1) ->
               let uu___246_18983 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___246_18983.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___246_18983.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___246_18983.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___246_18983.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____18994 -> s