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
  fun projectee  -> match projectee with | Beta  -> true | uu____13 -> false
let uu___is_Iota: step -> Prims.bool =
  fun projectee  -> match projectee with | Iota  -> true | uu____18 -> false
let uu___is_Zeta: step -> Prims.bool =
  fun projectee  -> match projectee with | Zeta  -> true | uu____23 -> false
let uu___is_Exclude: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____29 -> false
let __proj__Exclude__item___0: step -> step =
  fun projectee  -> match projectee with | Exclude _0 -> _0
let uu___is_WHNF: step -> Prims.bool =
  fun projectee  -> match projectee with | WHNF  -> true | uu____42 -> false
let uu___is_Primops: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____47 -> false
let uu___is_Eager_unfolding: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____52 -> false
let uu___is_Inlining: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____57 -> false
let uu___is_NoDeltaSteps: step -> Prims.bool =
  fun projectee  ->
    match projectee with | NoDeltaSteps  -> true | uu____62 -> false
let uu___is_UnfoldUntil: step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____68 -> false
let __proj__UnfoldUntil__item___0: step -> FStar_Syntax_Syntax.delta_depth =
  fun projectee  -> match projectee with | UnfoldUntil _0 -> _0
let uu___is_UnfoldTac: step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____81 -> false
let uu___is_PureSubtermsWithinComputations: step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____86 -> false
let uu___is_Simplify: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____91 -> false
let uu___is_EraseUniverses: step -> Prims.bool =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____96 -> false
let uu___is_AllowUnboundUniverses: step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____101 -> false
let uu___is_Reify: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____106 -> false
let uu___is_CompressUvars: step -> Prims.bool =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____111 -> false
let uu___is_NoFullNorm: step -> Prims.bool =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____116 -> false
let uu___is_CheckNoUvars: step -> Prims.bool =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____121 -> false
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
    match projectee with | Clos _0 -> true | uu____275 -> false
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
    match projectee with | Univ _0 -> true | uu____343 -> false
let __proj__Univ__item___0: closure -> FStar_Syntax_Syntax.universe =
  fun projectee  -> match projectee with | Univ _0 -> _0
let uu___is_Dummy: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____356 -> false
type env = closure Prims.list
let closure_to_string: closure -> Prims.string =
  fun uu___138_362  ->
    match uu___138_362 with
    | Clos (uu____363,t,uu____365,uu____366) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____387 -> "Univ"
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
    match projectee with | Arg _0 -> true | uu____604 -> false
let __proj__Arg__item___0:
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Arg _0 -> _0
let uu___is_UnivArgs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____642 -> false
let __proj__UnivArgs__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____680 -> false
let __proj__MemoLazy__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0
let uu___is_Match: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____739 -> false
let __proj__Match__item___0:
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Abs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____783 -> false
let __proj__Abs__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____839 -> false
let __proj__App__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Meta: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____875 -> false
let __proj__Meta__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Meta _0 -> _0
let uu___is_Let: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____909 -> false
let __proj__Let__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Steps: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Steps _0 -> true | uu____957 -> false
let __proj__Steps__item___0:
  stack_elt ->
    (steps,primitive_step Prims.list,FStar_TypeChecker_Env.delta_level
                                       Prims.list)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Steps _0 -> _0
let uu___is_Debug: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____1001 -> false
let __proj__Debug__item___0: stack_elt -> FStar_Syntax_Syntax.term =
  fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list
let mk:
  'Auu____1018 .
    'Auu____1018 ->
      FStar_Range.range -> 'Auu____1018 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r
let set_memo:
  'Auu____1175 'Auu____1176 .
    ('Auu____1176 FStar_Pervasives_Native.option,'Auu____1175) FStar_ST.mref
      -> 'Auu____1176 -> Prims.unit
  =
  fun r  ->
    fun t  ->
      let uu____1471 = FStar_ST.read r in
      match uu____1471 with
      | FStar_Pervasives_Native.Some uu____1572 ->
          failwith "Unexpected set_memo: thunk already evaluated"
      | FStar_Pervasives_Native.None  ->
          FStar_ST.write r (FStar_Pervasives_Native.Some t)
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____1679 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____1679 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___139_1687  ->
    match uu___139_1687 with
    | Arg (c,uu____1689,uu____1690) ->
        let uu____1691 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____1691
    | MemoLazy uu____1692 -> "MemoLazy"
    | Abs (uu____1699,bs,uu____1701,uu____1702,uu____1703) ->
        let uu____1708 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____1708
    | UnivArgs uu____1713 -> "UnivArgs"
    | Match uu____1720 -> "Match"
    | App (t,uu____1728,uu____1729) ->
        let uu____1730 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____1730
    | Meta (m,uu____1732) -> "Meta"
    | Let uu____1733 -> "Let"
    | Steps (uu____1742,uu____1743,uu____1744) -> "Steps"
    | Debug t ->
        let uu____1754 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____1754
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____1763 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____1763 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1781 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____1781 then f () else ()
let is_empty: 'Auu____1787 . 'Auu____1787 Prims.list -> Prims.bool =
  fun uu___140_1793  ->
    match uu___140_1793 with | [] -> true | uu____1796 -> false
let lookup_bvar:
  'Auu____1805 .
    'Auu____1805 Prims.list -> FStar_Syntax_Syntax.bv -> 'Auu____1805
  =
  fun env  ->
    fun x  ->
      try FStar_List.nth env x.FStar_Syntax_Syntax.index
      with
      | uu____1824 ->
          let uu____1825 =
            let uu____1826 = FStar_Syntax_Print.db_to_string x in
            FStar_Util.format1 "Failed to find %s\n" uu____1826 in
          failwith uu____1825
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
          let uu____1871 =
            FStar_List.fold_left
              (fun uu____1897  ->
                 fun u1  ->
                   match uu____1897 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____1922 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____1922 with
                        | (k_u,n1) ->
                            let uu____1937 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____1937
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____1871 with
          | (uu____1955,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____1980 = FStar_List.nth env x in
                 match uu____1980 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____1984 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____1993 ->
                   let uu____1994 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____1994
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____2000 when
              FStar_All.pipe_right cfg.steps
                (FStar_List.contains CheckNoUvars)
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____2009 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____2018 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____2025 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____2025 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____2042 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____2042 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____2050 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____2058 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____2058 with
                                  | (uu____2063,m) -> n1 <= m)) in
                        if uu____2050 then rest1 else us1
                    | uu____2068 -> us1)
               | uu____2073 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____2077 = aux u3 in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____2077 in
        let uu____2080 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____2080
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____2082 = aux u in
           match uu____2082 with
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
          (fun uu____2202  ->
             let uu____2203 = FStar_Syntax_Print.tag_of_term t in
             let uu____2204 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____2203
               uu____2204);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____2205 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____2209 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____2234 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____2235 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____2236 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____2237 ->
                  let uu____2254 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains CheckNoUvars) in
                  if uu____2254
                  then
                    let uu____2255 =
                      let uu____2256 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos in
                      let uu____2257 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____2256 uu____2257 in
                    failwith uu____2255
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____2260 =
                    let uu____2261 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____2261 in
                  mk uu____2260 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____2268 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____2268
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____2270 = lookup_bvar env x in
                  (match uu____2270 with
                   | Univ uu____2271 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____2275) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____2363 = closures_as_binders_delayed cfg env bs in
                  (match uu____2363 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____2397 =
                         let uu____2398 =
                           let uu____2415 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____2415) in
                         FStar_Syntax_Syntax.Tm_abs uu____2398 in
                       mk uu____2397 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____2446 = closures_as_binders_delayed cfg env bs in
                  (match uu____2446 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____2494 =
                    let uu____2507 =
                      let uu____2514 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____2514] in
                    closures_as_binders_delayed cfg env uu____2507 in
                  (match uu____2494 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____2536 =
                         let uu____2537 =
                           let uu____2544 =
                             let uu____2545 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____2545
                               FStar_Pervasives_Native.fst in
                           (uu____2544, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____2537 in
                       mk uu____2536 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____2636 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____2636
                    | FStar_Util.Inr c ->
                        let uu____2650 = close_comp cfg env c in
                        FStar_Util.Inr uu____2650 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____2666 =
                    let uu____2667 =
                      let uu____2694 = closure_as_term_delayed cfg env t11 in
                      (uu____2694, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____2667 in
                  mk uu____2666 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____2745 =
                    let uu____2746 =
                      let uu____2753 = closure_as_term_delayed cfg env t' in
                      let uu____2756 =
                        let uu____2757 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____2757 in
                      (uu____2753, uu____2756) in
                    FStar_Syntax_Syntax.Tm_meta uu____2746 in
                  mk uu____2745 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____2817 =
                    let uu____2818 =
                      let uu____2825 = closure_as_term_delayed cfg env t' in
                      let uu____2828 =
                        let uu____2829 =
                          let uu____2836 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____2836) in
                        FStar_Syntax_Syntax.Meta_monadic uu____2829 in
                      (uu____2825, uu____2828) in
                    FStar_Syntax_Syntax.Tm_meta uu____2818 in
                  mk uu____2817 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____2855 =
                    let uu____2856 =
                      let uu____2863 = closure_as_term_delayed cfg env t' in
                      let uu____2866 =
                        let uu____2867 =
                          let uu____2876 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____2876) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____2867 in
                      (uu____2863, uu____2866) in
                    FStar_Syntax_Syntax.Tm_meta uu____2856 in
                  mk uu____2855 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____2889 =
                    let uu____2890 =
                      let uu____2897 = closure_as_term_delayed cfg env t' in
                      (uu____2897, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____2890 in
                  mk uu____2889 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____2927  -> Dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let uu____2934 =
                    let uu____2945 = FStar_Syntax_Syntax.is_top_level [lb] in
                    if uu____2945
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       let uu____2964 =
                         closure_as_term cfg (Dummy :: env0) body in
                       ((FStar_Util.Inl
                           (let uu___155_2970 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___155_2970.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___155_2970.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____2964)) in
                  (match uu____2934 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___156_2986 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___156_2986.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___156_2986.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         } in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____2997,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____3032  -> fun env2  -> Dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____3039 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____3039
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____3047  -> fun env2  -> Dummy :: env2) lbs
                          env_univs in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let nm =
                      let uu____3057 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____3057
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         FStar_All.pipe_right
                           (let uu___157_3069 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___157_3069.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___157_3069.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41)) in
                    let uu___158_3070 = lb in
                    let uu____3071 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___158_3070.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___158_3070.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____3071
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____3089  -> fun env1  -> Dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____3168 =
                    match uu____3168 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____3233 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____3256 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____3322  ->
                                        fun uu____3323  ->
                                          match (uu____3322, uu____3323) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____3426 =
                                                norm_pat env3 p1 in
                                              (match uu____3426 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____3256 with
                               | (pats1,env3) ->
                                   ((let uu___159_3528 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___159_3528.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___160_3547 = x in
                                let uu____3548 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___160_3547.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___160_3547.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3548
                                } in
                              ((let uu___161_3556 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___161_3556.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___162_3561 = x in
                                let uu____3562 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___162_3561.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___162_3561.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3562
                                } in
                              ((let uu___163_3570 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___163_3570.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___164_3580 = x in
                                let uu____3581 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___164_3580.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___164_3580.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3581
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___165_3590 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___165_3590.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____3593 = norm_pat env1 pat in
                        (match uu____3593 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3628 =
                                     closure_as_term cfg env2 w in
                                   FStar_Pervasives_Native.Some uu____3628 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____3634 =
                    let uu____3635 =
                      let uu____3658 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____3658) in
                    FStar_Syntax_Syntax.Tm_match uu____3635 in
                  mk uu____3634 t1.FStar_Syntax_Syntax.pos))
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
        | uu____3740 -> closure_as_term cfg env t
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
        | uu____3764 ->
            FStar_List.map
              (fun uu____3783  ->
                 match uu____3783 with
                 | (x,imp) ->
                     let uu____3802 = closure_as_term_delayed cfg env x in
                     (uu____3802, imp)) args
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
        let uu____3818 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____3873  ->
                  fun uu____3874  ->
                    match (uu____3873, uu____3874) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___166_3956 = b in
                          let uu____3957 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___166_3956.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___166_3956.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____3957
                          } in
                        let env2 = Dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____3818 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____4038 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____4053 = closure_as_term_delayed cfg env t in
                 let uu____4054 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____4053 uu____4054
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____4067 = closure_as_term_delayed cfg env t in
                 let uu____4068 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____4067 uu____4068
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
                        (fun uu___141_4094  ->
                           match uu___141_4094 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____4098 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____4098
                           | f -> f)) in
                 let uu____4102 =
                   let uu___167_4103 = c1 in
                   let uu____4104 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____4104;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___167_4103.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____4102)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags  ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___142_4114  ->
            match uu___142_4114 with
            | FStar_Syntax_Syntax.DECREASES uu____4115 -> false
            | uu____4118 -> true))
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
                   (fun uu___143_4138  ->
                      match uu___143_4138 with
                      | FStar_Syntax_Syntax.DECREASES uu____4139 -> false
                      | uu____4142 -> true)) in
            let rc1 =
              let uu___168_4144 = rc in
              let uu____4145 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___168_4144.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____4145;
                FStar_Syntax_Syntax.residual_flags = flags
              } in
            FStar_Pervasives_Native.Some rc1
        | uu____4152 -> lopt
let built_in_primitive_steps: primitive_step Prims.list =
  let const_as_tm c p = mk (FStar_Syntax_Syntax.Tm_constant c) p in
  let int_as_const p i =
    let uu____4173 =
      let uu____4174 =
        let uu____4185 = FStar_Util.string_of_int i in
        (uu____4185, FStar_Pervasives_Native.None) in
      FStar_Const.Const_int uu____4174 in
    const_as_tm uu____4173 p in
  let bool_as_const p b = const_as_tm (FStar_Const.Const_bool b) p in
  let string_as_const p b =
    const_as_tm
      (FStar_Const.Const_string ((FStar_Util.bytes_of_string b), p)) p in
  let arg_as_int uu____4221 =
    match uu____4221 with
    | (a,uu____4229) ->
        let uu____4232 =
          let uu____4233 = FStar_Syntax_Subst.compress a in
          uu____4233.FStar_Syntax_Syntax.n in
        (match uu____4232 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (i,FStar_Pervasives_Native.None )) ->
             let uu____4249 = FStar_Util.int_of_string i in
             FStar_Pervasives_Native.Some uu____4249
         | uu____4250 -> FStar_Pervasives_Native.None) in
  let arg_as_bounded_int uu____4264 =
    match uu____4264 with
    | (a,uu____4276) ->
        let uu____4283 =
          let uu____4284 = FStar_Syntax_Subst.compress a in
          uu____4284.FStar_Syntax_Syntax.n in
        (match uu____4283 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____4294;
                FStar_Syntax_Syntax.vars = uu____4295;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____4297;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____4298;_},uu____4299)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____4338 =
               let uu____4343 = FStar_Util.int_of_string i in
               (fv1, uu____4343) in
             FStar_Pervasives_Native.Some uu____4338
         | uu____4348 -> FStar_Pervasives_Native.None) in
  let arg_as_bool uu____4362 =
    match uu____4362 with
    | (a,uu____4370) ->
        let uu____4373 =
          let uu____4374 = FStar_Syntax_Subst.compress a in
          uu____4374.FStar_Syntax_Syntax.n in
        (match uu____4373 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
             FStar_Pervasives_Native.Some b
         | uu____4380 -> FStar_Pervasives_Native.None) in
  let arg_as_char uu____4390 =
    match uu____4390 with
    | (a,uu____4398) ->
        let uu____4401 =
          let uu____4402 = FStar_Syntax_Subst.compress a in
          uu____4402.FStar_Syntax_Syntax.n in
        (match uu____4401 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
             FStar_Pervasives_Native.Some c
         | uu____4408 -> FStar_Pervasives_Native.None) in
  let arg_as_string uu____4418 =
    match uu____4418 with
    | (a,uu____4426) ->
        let uu____4429 =
          let uu____4430 = FStar_Syntax_Subst.compress a in
          uu____4430.FStar_Syntax_Syntax.n in
        (match uu____4429 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (bytes,uu____4436)) ->
             FStar_Pervasives_Native.Some (FStar_Util.string_of_bytes bytes)
         | uu____4441 -> FStar_Pervasives_Native.None) in
  let arg_as_list f uu____4467 =
    match uu____4467 with
    | (a,uu____4481) ->
        let rec sequence l =
          match l with
          | [] -> FStar_Pervasives_Native.Some []
          | (FStar_Pervasives_Native.None )::uu____4510 ->
              FStar_Pervasives_Native.None
          | (FStar_Pervasives_Native.Some x)::xs ->
              let uu____4527 = sequence xs in
              (match uu____4527 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some xs' ->
                   FStar_Pervasives_Native.Some (x :: xs')) in
        let uu____4547 = FStar_Syntax_Util.list_elements a in
        (match uu____4547 with
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some elts ->
             let uu____4565 =
               FStar_List.map
                 (fun x  ->
                    let uu____4575 = FStar_Syntax_Syntax.as_arg x in
                    f uu____4575) elts in
             sequence uu____4565) in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4613 = f a in FStar_Pervasives_Native.Some uu____4613
    | uu____4614 -> FStar_Pervasives_Native.None in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4664 = f a0 a1 in FStar_Pervasives_Native.Some uu____4664
    | uu____4665 -> FStar_Pervasives_Native.None in
  let unary_op as_a f r args =
    let uu____4714 = FStar_List.map as_a args in lift_unary (f r) uu____4714 in
  let binary_op as_a f r args =
    let uu____4770 = FStar_List.map as_a args in lift_binary (f r) uu____4770 in
  let as_primitive_step uu____4794 =
    match uu____4794 with
    | (l,arity,f) ->
        { name = l; arity; strong_reduction_ok = true; interpretation = f } in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  -> fun x  -> let uu____4842 = f x in int_as_const r uu____4842) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  -> let uu____4870 = f x y in int_as_const r uu____4870) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  -> fun x  -> let uu____4891 = f x in bool_as_const r uu____4891) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  -> let uu____4919 = f x y in bool_as_const r uu____4919) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  -> let uu____4947 = f x y in string_as_const r uu____4947) in
  let list_of_string' rng s =
    let name l =
      let uu____4961 =
        let uu____4962 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____4962 in
      mk uu____4961 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____4972 =
      let uu____4975 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____4975 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____4972 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in int_as_const rng r in
  let string_concat' rng args =
    match args with
    | a1::a2::[] ->
        let uu____5050 = arg_as_string a1 in
        (match uu____5050 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5056 = arg_as_list arg_as_string a2 in
             (match uu____5056 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____5069 = string_as_const rng r in
                  FStar_Pervasives_Native.Some uu____5069
              | uu____5070 -> FStar_Pervasives_Native.None)
         | uu____5075 -> FStar_Pervasives_Native.None)
    | uu____5078 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____5092 = FStar_Util.string_of_int i in
    string_as_const rng uu____5092 in
  let string_of_bool1 rng b =
    string_as_const rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____5108 = FStar_Util.string_of_int i in
    string_as_const rng uu____5108 in
  let string_of_bool2 rng b =
    string_as_const rng (if b then "true" else "false") in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r in
  let range_of1 uu____5138 args =
    match args with
    | uu____5150::(t,uu____5152)::[] ->
        let uu____5181 = term_of_range t.FStar_Syntax_Syntax.pos in
        FStar_Pervasives_Native.Some uu____5181
    | uu____5186 -> FStar_Pervasives_Native.None in
  let set_range_of1 r args =
    match args with
    | uu____5224::(t,uu____5226)::({
                                     FStar_Syntax_Syntax.n =
                                       FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_range r1);
                                     FStar_Syntax_Syntax.pos = uu____5228;
                                     FStar_Syntax_Syntax.vars = uu____5229;_},uu____5230)::[]
        ->
        FStar_Pervasives_Native.Some
          (let uu___169_5272 = t in
           {
             FStar_Syntax_Syntax.n = (uu___169_5272.FStar_Syntax_Syntax.n);
             FStar_Syntax_Syntax.pos = r1;
             FStar_Syntax_Syntax.vars =
               (uu___169_5272.FStar_Syntax_Syntax.vars)
           })
    | uu____5275 -> FStar_Pervasives_Native.None in
  let mk_range1 r args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____5356 =
          let uu____5377 = arg_as_string fn in
          let uu____5380 = arg_as_int from_line in
          let uu____5383 = arg_as_int from_col in
          let uu____5386 = arg_as_int to_line in
          let uu____5389 = arg_as_int to_col in
          (uu____5377, uu____5380, uu____5383, uu____5386, uu____5389) in
        (match uu____5356 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r1 =
               let uu____5420 = FStar_Range.mk_pos from_l from_c in
               let uu____5421 = FStar_Range.mk_pos to_l to_c in
               FStar_Range.mk_range fn1 uu____5420 uu____5421 in
             let uu____5422 = term_of_range r1 in
             FStar_Pervasives_Native.Some uu____5422
         | uu____5427 -> FStar_Pervasives_Native.None)
    | uu____5448 -> FStar_Pervasives_Native.None in
  let decidable_eq neg rng args =
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) rng in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) rng in
    match args with
    | (_typ,uu____5478)::(a1,uu____5480)::(a2,uu____5482)::[] ->
        let uu____5519 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____5519 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____5532 -> FStar_Pervasives_Native.None)
    | uu____5533 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____5551 =
      let uu____5566 =
        let uu____5581 =
          let uu____5596 =
            let uu____5611 =
              let uu____5626 =
                let uu____5641 =
                  let uu____5656 =
                    let uu____5671 =
                      let uu____5686 =
                        let uu____5701 =
                          let uu____5716 =
                            let uu____5731 =
                              let uu____5746 =
                                let uu____5761 =
                                  let uu____5776 =
                                    let uu____5791 =
                                      let uu____5806 =
                                        let uu____5821 =
                                          let uu____5836 =
                                            let uu____5851 =
                                              let uu____5864 =
                                                FStar_Parser_Const.p2l
                                                  ["FStar";
                                                  "String";
                                                  "list_of_string"] in
                                              (uu____5864,
                                                (Prims.parse_int "1"),
                                                (unary_op arg_as_string
                                                   list_of_string')) in
                                            let uu____5871 =
                                              let uu____5886 =
                                                let uu____5899 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "string_of_list"] in
                                                (uu____5899,
                                                  (Prims.parse_int "1"),
                                                  (unary_op
                                                     (arg_as_list arg_as_char)
                                                     string_of_list')) in
                                              let uu____5908 =
                                                let uu____5923 =
                                                  let uu____5942 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "concat"] in
                                                  (uu____5942,
                                                    (Prims.parse_int "2"),
                                                    string_concat') in
                                                let uu____5955 =
                                                  let uu____5976 =
                                                    let uu____5997 =
                                                      FStar_Parser_Const.p2l
                                                        ["Prims"; "range_of"] in
                                                    (uu____5997,
                                                      (Prims.parse_int "2"),
                                                      range_of1) in
                                                  let uu____6012 =
                                                    let uu____6035 =
                                                      let uu____6056 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "set_range_of"] in
                                                      (uu____6056,
                                                        (Prims.parse_int "3"),
                                                        set_range_of1) in
                                                    let uu____6071 =
                                                      let uu____6094 =
                                                        let uu____6113 =
                                                          FStar_Parser_Const.p2l
                                                            ["Prims";
                                                            "mk_range"] in
                                                        (uu____6113,
                                                          (Prims.parse_int
                                                             "5"), mk_range1) in
                                                      [uu____6094] in
                                                    uu____6035 :: uu____6071 in
                                                  uu____5976 :: uu____6012 in
                                                uu____5923 :: uu____5955 in
                                              uu____5886 :: uu____5908 in
                                            uu____5851 :: uu____5871 in
                                          (FStar_Parser_Const.op_notEq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq true)) ::
                                            uu____5836 in
                                        (FStar_Parser_Const.op_Eq,
                                          (Prims.parse_int "3"),
                                          (decidable_eq false)) :: uu____5821 in
                                      (FStar_Parser_Const.string_compare,
                                        (Prims.parse_int "2"),
                                        (binary_op arg_as_string
                                           string_compare'))
                                        :: uu____5806 in
                                    (FStar_Parser_Const.string_of_bool_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_bool string_of_bool2))
                                      :: uu____5791 in
                                  (FStar_Parser_Const.string_of_int_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_int string_of_int2)) ::
                                    uu____5776 in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____5761 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5746 in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____5731 in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____5716 in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____5701 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____5686 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
                      :: uu____5671 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____5656 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____5641 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____5626 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____5611 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____5596 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____5581 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____5566 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____5551 in
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
      let uu____6720 =
        let uu____6721 =
          let uu____6722 = FStar_Syntax_Syntax.as_arg c in [uu____6722] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6721 in
      uu____6720 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____6757 =
              let uu____6770 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____6770, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____6789  ->
                        fun uu____6790  ->
                          match (uu____6789, uu____6790) with
                          | ((int_to_t1,x),(uu____6809,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____6819 =
              let uu____6834 =
                let uu____6847 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____6847, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____6866  ->
                          fun uu____6867  ->
                            match (uu____6866, uu____6867) with
                            | ((int_to_t1,x),(uu____6886,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____6896 =
                let uu____6911 =
                  let uu____6924 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____6924, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____6943  ->
                            fun uu____6944  ->
                              match (uu____6943, uu____6944) with
                              | ((int_to_t1,x),(uu____6963,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____6911] in
              uu____6834 :: uu____6896 in
            uu____6757 :: uu____6819)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop r args =
    match args with
    | (_typ,uu____7059)::(a1,uu____7061)::(a2,uu____7063)::[] ->
        let uu____7100 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____7100 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___170_7106 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___170_7106.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___170_7106.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___171_7110 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___171_7110.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___171_7110.FStar_Syntax_Syntax.vars)
                })
         | uu____7111 -> FStar_Pervasives_Native.None)
    | (_typ,uu____7113)::uu____7114::(a1,uu____7116)::(a2,uu____7118)::[] ->
        let uu____7167 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____7167 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___170_7173 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___170_7173.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___170_7173.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___171_7177 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___171_7177.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___171_7177.FStar_Syntax_Syntax.vars)
                })
         | uu____7178 -> FStar_Pervasives_Native.None)
    | uu____7179 -> failwith "Unexpected number of arguments" in
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
      let uu____7192 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops cfg.steps) in
      if uu____7192
      then tm
      else
        (let uu____7194 = FStar_Syntax_Util.head_and_args tm in
         match uu____7194 with
         | (head1,args) ->
             let uu____7231 =
               let uu____7232 = FStar_Syntax_Util.un_uinst head1 in
               uu____7232.FStar_Syntax_Syntax.n in
             (match uu____7231 with
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____7236 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps in
                  (match uu____7236 with
                   | FStar_Pervasives_Native.None  -> tm
                   | FStar_Pervasives_Native.Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then tm
                       else
                         (let uu____7249 =
                            prim_step.interpretation
                              head1.FStar_Syntax_Syntax.pos args in
                          match uu____7249 with
                          | FStar_Pervasives_Native.None  -> tm
                          | FStar_Pervasives_Native.Some reduced -> reduced))
              | uu____7253 -> tm))
let reduce_equality:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___172_7264 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___172_7264.tcenv);
           delta_level = (uu___172_7264.delta_level);
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
        let uu___173_7288 = t in
        {
          FStar_Syntax_Syntax.n = (uu___173_7288.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___173_7288.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid ->
            FStar_Pervasives_Native.Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid ->
            FStar_Pervasives_Native.Some false
        | uu____7305 -> FStar_Pervasives_Native.None in
      let simplify arg = ((simp_t (FStar_Pervasives_Native.fst arg)), arg) in
      let tm1 = reduce_primops cfg tm in
      let uu____7345 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps) in
      if uu____7345
      then tm1
      else
        (match tm1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.pos = uu____7348;
                     FStar_Syntax_Syntax.vars = uu____7349;_},uu____7350);
                FStar_Syntax_Syntax.pos = uu____7351;
                FStar_Syntax_Syntax.vars = uu____7352;_},args)
             ->
             let uu____7378 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
             if uu____7378
             then
               let uu____7379 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____7379 with
                | (FStar_Pervasives_Native.Some (true ),uu____7434)::
                    (uu____7435,(arg,uu____7437))::[] -> arg
                | (uu____7502,(arg,uu____7504))::(FStar_Pervasives_Native.Some
                                                  (true ),uu____7505)::[]
                    -> arg
                | (FStar_Pervasives_Native.Some (false ),uu____7570)::uu____7571::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____7634::(FStar_Pervasives_Native.Some (false
                               ),uu____7635)::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____7698 -> tm1)
             else
               (let uu____7714 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
                if uu____7714
                then
                  let uu____7715 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____7715 with
                  | (FStar_Pervasives_Native.Some (true ),uu____7770)::uu____7771::[]
                      -> w FStar_Syntax_Util.t_true
                  | uu____7834::(FStar_Pervasives_Native.Some (true
                                 ),uu____7835)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____7898)::
                      (uu____7899,(arg,uu____7901))::[] -> arg
                  | (uu____7966,(arg,uu____7968))::(FStar_Pervasives_Native.Some
                                                    (false ),uu____7969)::[]
                      -> arg
                  | uu____8034 -> tm1
                else
                  (let uu____8050 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.imp_lid in
                   if uu____8050
                   then
                     let uu____8051 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____8051 with
                     | uu____8106::(FStar_Pervasives_Native.Some (true
                                    ),uu____8107)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____8170)::uu____8171::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____8234)::
                         (uu____8235,(arg,uu____8237))::[] -> arg
                     | (uu____8302,(p,uu____8304))::(uu____8305,(q,uu____8307))::[]
                         ->
                         let uu____8372 = FStar_Syntax_Util.term_eq p q in
                         (if uu____8372
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____8374 -> tm1
                   else
                     (let uu____8390 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____8390
                      then
                        let uu____8391 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____8391 with
                        | (FStar_Pervasives_Native.Some (true ),uu____8446)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____8485)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____8524 -> tm1
                      else
                        (let uu____8540 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____8540
                         then
                           match args with
                           | (t,uu____8542)::[] ->
                               let uu____8559 =
                                 let uu____8560 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____8560.FStar_Syntax_Syntax.n in
                               (match uu____8559 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____8563::[],body,uu____8565) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____8592 -> tm1)
                                | uu____8595 -> tm1)
                           | (uu____8596,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____8597))::
                               (t,uu____8599)::[] ->
                               let uu____8638 =
                                 let uu____8639 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____8639.FStar_Syntax_Syntax.n in
                               (match uu____8638 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____8642::[],body,uu____8644) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____8671 -> tm1)
                                | uu____8674 -> tm1)
                           | uu____8675 -> tm1
                         else
                           (let uu____8685 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____8685
                            then
                              match args with
                              | (t,uu____8687)::[] ->
                                  let uu____8704 =
                                    let uu____8705 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____8705.FStar_Syntax_Syntax.n in
                                  (match uu____8704 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____8708::[],body,uu____8710) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____8737 -> tm1)
                                   | uu____8740 -> tm1)
                              | (uu____8741,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____8742))::
                                  (t,uu____8744)::[] ->
                                  let uu____8783 =
                                    let uu____8784 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____8784.FStar_Syntax_Syntax.n in
                                  (match uu____8783 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____8787::[],body,uu____8789) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____8816 -> tm1)
                                   | uu____8819 -> tm1)
                              | uu____8820 -> tm1
                            else reduce_equality cfg tm1)))))
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                FStar_Syntax_Syntax.pos = uu____8831;
                FStar_Syntax_Syntax.vars = uu____8832;_},args)
             ->
             let uu____8854 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
             if uu____8854
             then
               let uu____8855 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____8855 with
                | (FStar_Pervasives_Native.Some (true ),uu____8910)::
                    (uu____8911,(arg,uu____8913))::[] -> arg
                | (uu____8978,(arg,uu____8980))::(FStar_Pervasives_Native.Some
                                                  (true ),uu____8981)::[]
                    -> arg
                | (FStar_Pervasives_Native.Some (false ),uu____9046)::uu____9047::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____9110::(FStar_Pervasives_Native.Some (false
                               ),uu____9111)::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____9174 -> tm1)
             else
               (let uu____9190 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
                if uu____9190
                then
                  let uu____9191 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____9191 with
                  | (FStar_Pervasives_Native.Some (true ),uu____9246)::uu____9247::[]
                      -> w FStar_Syntax_Util.t_true
                  | uu____9310::(FStar_Pervasives_Native.Some (true
                                 ),uu____9311)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____9374)::
                      (uu____9375,(arg,uu____9377))::[] -> arg
                  | (uu____9442,(arg,uu____9444))::(FStar_Pervasives_Native.Some
                                                    (false ),uu____9445)::[]
                      -> arg
                  | uu____9510 -> tm1
                else
                  (let uu____9526 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.imp_lid in
                   if uu____9526
                   then
                     let uu____9527 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____9527 with
                     | uu____9582::(FStar_Pervasives_Native.Some (true
                                    ),uu____9583)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____9646)::uu____9647::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____9710)::
                         (uu____9711,(arg,uu____9713))::[] -> arg
                     | (uu____9778,(p,uu____9780))::(uu____9781,(q,uu____9783))::[]
                         ->
                         let uu____9848 = FStar_Syntax_Util.term_eq p q in
                         (if uu____9848
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____9850 -> tm1
                   else
                     (let uu____9866 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____9866
                      then
                        let uu____9867 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____9867 with
                        | (FStar_Pervasives_Native.Some (true ),uu____9922)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____9961)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____10000 -> tm1
                      else
                        (let uu____10016 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____10016
                         then
                           match args with
                           | (t,uu____10018)::[] ->
                               let uu____10035 =
                                 let uu____10036 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____10036.FStar_Syntax_Syntax.n in
                               (match uu____10035 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____10039::[],body,uu____10041) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____10068 -> tm1)
                                | uu____10071 -> tm1)
                           | (uu____10072,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____10073))::
                               (t,uu____10075)::[] ->
                               let uu____10114 =
                                 let uu____10115 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____10115.FStar_Syntax_Syntax.n in
                               (match uu____10114 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____10118::[],body,uu____10120) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____10147 -> tm1)
                                | uu____10150 -> tm1)
                           | uu____10151 -> tm1
                         else
                           (let uu____10161 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____10161
                            then
                              match args with
                              | (t,uu____10163)::[] ->
                                  let uu____10180 =
                                    let uu____10181 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____10181.FStar_Syntax_Syntax.n in
                                  (match uu____10180 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____10184::[],body,uu____10186) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____10213 -> tm1)
                                   | uu____10216 -> tm1)
                              | (uu____10217,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____10218))::
                                  (t,uu____10220)::[] ->
                                  let uu____10259 =
                                    let uu____10260 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____10260.FStar_Syntax_Syntax.n in
                                  (match uu____10259 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____10263::[],body,uu____10265) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____10292 -> tm1)
                                   | uu____10295 -> tm1)
                              | uu____10296 -> tm1
                            else reduce_equality cfg tm1)))))
         | uu____10306 -> tm1)
let is_norm_request:
  'Auu____10313 .
    FStar_Syntax_Syntax.term -> 'Auu____10313 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10326 =
        let uu____10333 =
          let uu____10334 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10334.FStar_Syntax_Syntax.n in
        (uu____10333, args) in
      match uu____10326 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10340::uu____10341::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10345::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | uu____10348 -> false
let get_norm_request:
  'Auu____10361 'Auu____10362 .
    ('Auu____10362,'Auu____10361) FStar_Pervasives_Native.tuple2 Prims.list
      -> 'Auu____10362
  =
  fun args  ->
    match args with
    | uu____10379::(tm,uu____10381)::[] -> tm
    | (tm,uu____10399)::[] -> tm
    | uu____10408 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___144_10420  ->
    match uu___144_10420 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.pos = uu____10423;
           FStar_Syntax_Syntax.vars = uu____10424;_},uu____10425,uu____10426))::uu____10427
        -> true
    | uu____10434 -> false
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
            (fun uu____10569  ->
               let uu____10570 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____10571 = FStar_Syntax_Print.term_to_string t1 in
               let uu____10572 =
                 let uu____10573 =
                   let uu____10576 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____10576 in
                 stack_to_string uu____10573 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____10570
                 uu____10571 uu____10572);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____10599 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____10624 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____10641 =
                 let uu____10642 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____10643 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____10642 uu____10643 in
               failwith uu____10641
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____10644 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____10661 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____10662 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10663;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____10664;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10667;
                 FStar_Syntax_Syntax.fv_delta = uu____10668;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10669;
                 FStar_Syntax_Syntax.fv_delta = uu____10670;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____10671);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (FStar_Syntax_Util.is_fstar_tactics_embed hd1) ||
                 (FStar_Syntax_Util.is_fstar_tactics_by_tactic hd1)
               ->
               let args1 = closures_as_args_delayed cfg env args in
               let hd2 = closure_as_term cfg env hd1 in
               let t2 =
                 let uu___174_10713 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___174_10713.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___174_10713.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____10746 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____10746) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let tm = get_norm_request args in
               let s =
                 [Reify;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 Primops] in
               let cfg' =
                 let uu___175_10762 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___175_10762.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___175_10762.primitive_steps)
                 } in
               let stack' = (Debug t1) ::
                 (Steps
                    ((cfg.steps), (cfg.primitive_steps), (cfg.delta_level)))
                 :: stack1 in
               norm cfg' env stack' tm
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____10770;
                  FStar_Syntax_Syntax.vars = uu____10771;_},a1::a2::rest)
               ->
               let uu____10819 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____10819 with
                | (hd1,uu____10835) ->
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
                    (FStar_Const.Const_reflect uu____10900);
                  FStar_Syntax_Syntax.pos = uu____10901;
                  FStar_Syntax_Syntax.vars = uu____10902;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____10934 = FStar_List.tl stack1 in
               norm cfg env uu____10934 (FStar_Pervasives_Native.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____10937;
                  FStar_Syntax_Syntax.vars = uu____10938;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____10970 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____10970 with
                | (reify_head,uu____10986) ->
                    let a1 =
                      let uu____11008 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (FStar_Pervasives_Native.fst a) in
                      FStar_Syntax_Subst.compress uu____11008 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____11011);
                            FStar_Syntax_Syntax.pos = uu____11012;
                            FStar_Syntax_Syntax.vars = uu____11013;_},a2::[])
                         ->
                         norm cfg env stack1 (FStar_Pervasives_Native.fst a2)
                     | uu____11047 ->
                         let stack2 =
                           (App
                              (reify_head, FStar_Pervasives_Native.None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11057 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____11057
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11064 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11064
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____11067 =
                      let uu____11074 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11074, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11067 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___145_11088  ->
                         match uu___145_11088 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11091 =
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
                 if uu____11091 then false else should_delta in
               if Prims.op_Negation should_delta1
               then rebuild cfg env stack1 t1
               else
                 (let r_env =
                    let uu____11095 = FStar_Syntax_Syntax.range_of_fv f in
                    FStar_TypeChecker_Env.set_range cfg.tcenv uu____11095 in
                  let uu____11096 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  match uu____11096 with
                  | FStar_Pervasives_Native.None  ->
                      (log cfg
                         (fun uu____11109  ->
                            FStar_Util.print "Tm_fvar case 2\n" []);
                       rebuild cfg env stack1 t1)
                  | FStar_Pervasives_Native.Some (us,t2) ->
                      (log cfg
                         (fun uu____11120  ->
                            let uu____11121 =
                              FStar_Syntax_Print.term_to_string t0 in
                            let uu____11122 =
                              FStar_Syntax_Print.term_to_string t2 in
                            FStar_Util.print2 ">>> Unfolded %s to %s\n"
                              uu____11121 uu____11122);
                       (let t3 =
                          let uu____11124 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 (UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant)) in
                          if uu____11124
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
                          | (UnivArgs (us',uu____11134))::stack2 ->
                              let env1 =
                                FStar_All.pipe_right us'
                                  (FStar_List.fold_left
                                     (fun env1  -> fun u  -> (Univ u) :: env1)
                                     env) in
                              norm cfg env1 stack2 t3
                          | uu____11157 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack1 t3
                          | uu____11158 ->
                              let uu____11159 =
                                let uu____11160 =
                                  FStar_Syntax_Print.lid_to_string
                                    (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                FStar_Util.format1
                                  "Impossible: missing universe instantiation on %s"
                                  uu____11160 in
                              failwith uu____11159
                        else norm cfg env stack1 t3)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11163 = lookup_bvar env x in
               (match uu____11163 with
                | Univ uu____11164 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11189 = FStar_ST.read r in
                      (match uu____11189 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11270  ->
                                 let uu____11271 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____11272 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11271
                                   uu____11272);
                            (let uu____11273 =
                               let uu____11274 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____11274.FStar_Syntax_Syntax.n in
                             match uu____11273 with
                             | FStar_Syntax_Syntax.Tm_abs uu____11277 ->
                                 norm cfg env2 stack1 t'
                             | uu____11294 -> rebuild cfg env2 stack1 t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____11346)::uu____11347 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11356)::uu____11357 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11367,uu____11368))::stack_rest ->
                    (match c with
                     | Univ uu____11372 -> norm cfg (c :: env) stack_rest t1
                     | uu____11373 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____11378::[] ->
                              (match lopt with
                               | FStar_Pervasives_Native.None  when
                                   FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____11394  ->
                                         let uu____11395 =
                                           closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____11395);
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
                                           (fun uu___146_11400  ->
                                              match uu___146_11400 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____11401 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____11405  ->
                                         let uu____11406 =
                                           closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____11406);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____11407 when
                                   (FStar_All.pipe_right cfg.steps
                                      (FStar_List.contains Reify))
                                     ||
                                     (FStar_All.pipe_right cfg.steps
                                        (FStar_List.contains CheckNoUvars))
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____11410 ->
                                   let cfg1 =
                                     let uu___176_11414 = cfg in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___176_11414.tcenv);
                                       delta_level =
                                         (uu___176_11414.delta_level);
                                       primitive_steps =
                                         (uu___176_11414.primitive_steps)
                                     } in
                                   let uu____11415 =
                                     closure_as_term cfg1 env t1 in
                                   rebuild cfg1 env stack1 uu____11415)
                          | uu____11416::tl1 ->
                              (log cfg
                                 (fun uu____11435  ->
                                    let uu____11436 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11436);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___177_11466 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___177_11466.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____11527  ->
                          let uu____11528 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11528);
                     norm cfg env stack2 t1)
                | (Debug uu____11529)::uu____11530 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11533 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11533
                    else
                      (let uu____11535 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11535 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11559  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11575 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11575
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11585 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11585)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___178_11590 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___178_11590.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___178_11590.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11591 -> lopt in
                           (log cfg
                              (fun uu____11597  ->
                                 let uu____11598 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11598);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___179_11611 = cfg in
                               let uu____11612 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___179_11611.steps);
                                 tcenv = (uu___179_11611.tcenv);
                                 delta_level = (uu___179_11611.delta_level);
                                 primitive_steps = uu____11612
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____11621)::uu____11622 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11629 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11629
                    else
                      (let uu____11631 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11631 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11655  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11671 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11671
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11681 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11681)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___178_11686 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___178_11686.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___178_11686.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11687 -> lopt in
                           (log cfg
                              (fun uu____11693  ->
                                 let uu____11694 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11694);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___179_11707 = cfg in
                               let uu____11708 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___179_11707.steps);
                                 tcenv = (uu___179_11707.tcenv);
                                 delta_level = (uu___179_11707.delta_level);
                                 primitive_steps = uu____11708
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____11717)::uu____11718 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11729 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11729
                    else
                      (let uu____11731 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11731 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11755  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11771 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11771
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11781 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11781)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___178_11786 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___178_11786.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___178_11786.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11787 -> lopt in
                           (log cfg
                              (fun uu____11793  ->
                                 let uu____11794 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11794);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___179_11807 = cfg in
                               let uu____11808 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___179_11807.steps);
                                 tcenv = (uu___179_11807.tcenv);
                                 delta_level = (uu___179_11807.delta_level);
                                 primitive_steps = uu____11808
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____11817)::uu____11818 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11827 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11827
                    else
                      (let uu____11829 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11829 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11853  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11869 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11869
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11879 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11879)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___178_11884 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___178_11884.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___178_11884.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11885 -> lopt in
                           (log cfg
                              (fun uu____11891  ->
                                 let uu____11892 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11892);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___179_11905 = cfg in
                               let uu____11906 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___179_11905.steps);
                                 tcenv = (uu___179_11905.tcenv);
                                 delta_level = (uu___179_11905.delta_level);
                                 primitive_steps = uu____11906
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____11915)::uu____11916 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11931 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11931
                    else
                      (let uu____11933 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11933 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11957  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11973 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11973
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11983 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11983)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___178_11988 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___178_11988.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___178_11988.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11989 -> lopt in
                           (log cfg
                              (fun uu____11995  ->
                                 let uu____11996 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11996);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___179_12009 = cfg in
                               let uu____12010 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___179_12009.steps);
                                 tcenv = (uu___179_12009.tcenv);
                                 delta_level = (uu___179_12009.delta_level);
                                 primitive_steps = uu____12010
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12019 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12019
                    else
                      (let uu____12021 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12021 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12045  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12061 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12061
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12071 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12071)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___178_12076 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___178_12076.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___178_12076.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12077 -> lopt in
                           (log cfg
                              (fun uu____12083  ->
                                 let uu____12084 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12084);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___179_12097 = cfg in
                               let uu____12098 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___179_12097.steps);
                                 tcenv = (uu___179_12097.tcenv);
                                 delta_level = (uu___179_12097.delta_level);
                                 primitive_steps = uu____12098
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
                      (fun uu____12145  ->
                         fun stack2  ->
                           match uu____12145 with
                           | (a,aq) ->
                               let uu____12157 =
                                 let uu____12158 =
                                   let uu____12165 =
                                     let uu____12166 =
                                       let uu____12185 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____12185, false) in
                                     Clos uu____12166 in
                                   (uu____12165, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____12158 in
                               uu____12157 :: stack2) args) in
               (log cfg
                  (fun uu____12237  ->
                     let uu____12238 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12238);
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
                             ((let uu___180_12262 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___180_12262.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___180_12262.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____12263 ->
                      let uu____12268 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12268)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____12271 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____12271 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____12296 =
                          let uu____12297 =
                            let uu____12304 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___181_12306 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___181_12306.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___181_12306.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12304) in
                          FStar_Syntax_Syntax.Tm_refine uu____12297 in
                        mk uu____12296 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____12325 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____12325
               else
                 (let uu____12327 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____12327 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12335 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12347  -> Dummy :: env1) env) in
                        norm_comp cfg uu____12335 c1 in
                      let t2 =
                        let uu____12357 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____12357 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____12416)::uu____12417 -> norm cfg env stack1 t11
                | (Arg uu____12426)::uu____12427 -> norm cfg env stack1 t11
                | (App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____12436;
                       FStar_Syntax_Syntax.vars = uu____12437;_},uu____12438,uu____12439))::uu____12440
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____12447)::uu____12448 ->
                    norm cfg env stack1 t11
                | uu____12457 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____12461  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____12478 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____12478
                        | FStar_Util.Inr c ->
                            let uu____12486 = norm_comp cfg env c in
                            FStar_Util.Inr uu____12486 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____12492 =
                        let uu____12493 =
                          let uu____12494 =
                            let uu____12521 = FStar_Syntax_Util.unascribe t12 in
                            (uu____12521, (tc1, tacopt1), l) in
                          FStar_Syntax_Syntax.Tm_ascribed uu____12494 in
                        mk uu____12493 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____12492)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____12597,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____12598;
                               FStar_Syntax_Syntax.lbunivs = uu____12599;
                               FStar_Syntax_Syntax.lbtyp = uu____12600;
                               FStar_Syntax_Syntax.lbeff = uu____12601;
                               FStar_Syntax_Syntax.lbdef = uu____12602;_}::uu____12603),uu____12604)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____12640 =
                 (let uu____12643 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____12643) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____12645 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____12645))) in
               if uu____12640
               then
                 let env1 =
                   let uu____12649 =
                     let uu____12650 =
                       let uu____12669 =
                         FStar_Util.mk_ref FStar_Pervasives_Native.None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____12669,
                         false) in
                     Clos uu____12650 in
                   uu____12649 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____12721 =
                    let uu____12726 =
                      let uu____12727 =
                        let uu____12728 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____12728
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____12727] in
                    FStar_Syntax_Subst.open_term uu____12726 body in
                  match uu____12721 with
                  | (bs,body1) ->
                      let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                      let lbname =
                        let x =
                          let uu____12742 = FStar_List.hd bs in
                          FStar_Pervasives_Native.fst uu____12742 in
                        FStar_Util.Inl
                          (let uu___182_12752 = x in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___182_12752.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___182_12752.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = ty
                           }) in
                      let lb1 =
                        let uu___183_12754 = lb in
                        let uu____12755 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = lbname;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___183_12754.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = ty;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___183_12754.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____12755
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____12772  -> Dummy :: env1)
                             env) in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let ((true ,lbs),body) when
               FStar_List.contains CompressUvars cfg.steps ->
               let uu____12795 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____12795 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____12831 =
                               let uu___184_12832 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___184_12832.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___184_12832.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____12831 in
                           let uu____12833 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____12833 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____12853 =
                                   FStar_List.map (fun uu____12857  -> Dummy)
                                     lbs1 in
                                 let uu____12858 =
                                   let uu____12861 =
                                     FStar_List.map
                                       (fun uu____12869  -> Dummy) xs1 in
                                   FStar_List.append uu____12861 env in
                                 FStar_List.append uu____12853 uu____12858 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____12881 =
                                       let uu___185_12882 = rc in
                                       let uu____12883 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___185_12882.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____12883;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___185_12882.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____12881
                                 | uu____12890 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___186_12894 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___186_12894.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___186_12894.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____12898 =
                        FStar_List.map (fun uu____12902  -> Dummy) lbs2 in
                      FStar_List.append uu____12898 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____12904 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____12904 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___187_12920 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___187_12920.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___187_12920.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____12947 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____12947
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____12966 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13017  ->
                        match uu____13017 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____13090 =
                                let uu___188_13091 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___188_13091.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___188_13091.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____13090 in
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
               (match uu____12966 with
                | (rec_env,memos,uu____13219) ->
                    let uu____13248 =
                      FStar_List.map2
                        (fun lb  ->
                           fun memo  ->
                             FStar_ST.write memo
                               (FStar_Pervasives_Native.Some
                                  (rec_env, (lb.FStar_Syntax_Syntax.lbdef))))
                        (FStar_Pervasives_Native.snd lbs) memos in
                    let body_env =
                      FStar_List.fold_right
                        (fun lb  ->
                           fun env1  ->
                             let uu____13653 =
                               let uu____13654 =
                                 let uu____13673 =
                                   FStar_Util.mk_ref
                                     FStar_Pervasives_Native.None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____13673, false) in
                               Clos uu____13654 in
                             uu____13653 :: env1)
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
                             FStar_Syntax_Syntax.pos = uu____13741;
                             FStar_Syntax_Syntax.vars = uu____13742;_},uu____13743,uu____13744))::uu____13745
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____13752 -> false in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____13762 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____13762
                        then
                          let uu___189_13763 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___189_13763.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps =
                              (uu___189_13763.primitive_steps)
                          }
                        else
                          (let uu___190_13765 = cfg in
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___190_13765.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta];
                             primitive_steps =
                               (uu___190_13765.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____13767 =
                         let uu____13768 = FStar_Syntax_Subst.compress head1 in
                         uu____13768.FStar_Syntax_Syntax.n in
                       match uu____13767 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____13786 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____13786 with
                            | (uu____13787,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____13793 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____13801 =
                                         let uu____13802 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____13802.FStar_Syntax_Syntax.n in
                                       match uu____13801 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____13808,uu____13809))
                                           ->
                                           let uu____13818 =
                                             let uu____13819 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____13819.FStar_Syntax_Syntax.n in
                                           (match uu____13818 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____13825,msrc,uu____13827))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____13836 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____13836
                                            | uu____13837 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____13838 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____13839 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____13839 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___191_13844 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___191_13844.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___191_13844.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___191_13844.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____13845 =
                                            FStar_List.tl stack1 in
                                          let uu____13846 =
                                            let uu____13847 =
                                              let uu____13850 =
                                                let uu____13851 =
                                                  let uu____13864 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____13864) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____13851 in
                                              FStar_Syntax_Syntax.mk
                                                uu____13850 in
                                            uu____13847
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____13845
                                            uu____13846
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____13880 =
                                            let uu____13881 = is_return body in
                                            match uu____13881 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____13885;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____13886;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____13891 -> false in
                                          if uu____13880
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
                                               let uu____13915 =
                                                 let uu____13918 =
                                                   let uu____13919 =
                                                     let uu____13936 =
                                                       let uu____13939 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____13939] in
                                                     (uu____13936, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc)) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____13919 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____13918 in
                                               uu____13915
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____13955 =
                                                 let uu____13956 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____13956.FStar_Syntax_Syntax.n in
                                               match uu____13955 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____13962::uu____13963::[])
                                                   ->
                                                   let uu____13970 =
                                                     let uu____13973 =
                                                       let uu____13974 =
                                                         let uu____13981 =
                                                           let uu____13984 =
                                                             let uu____13985
                                                               =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____13985 in
                                                           let uu____13986 =
                                                             let uu____13989
                                                               =
                                                               let uu____13990
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____13990 in
                                                             [uu____13989] in
                                                           uu____13984 ::
                                                             uu____13986 in
                                                         (bind1, uu____13981) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____13974 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____13973 in
                                                   uu____13970
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____13998 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____14004 =
                                                 let uu____14007 =
                                                   let uu____14008 =
                                                     let uu____14023 =
                                                       let uu____14026 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____14027 =
                                                         let uu____14030 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____14031 =
                                                           let uu____14034 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____14035 =
                                                             let uu____14038
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____14039
                                                               =
                                                               let uu____14042
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____14043
                                                                 =
                                                                 let uu____14046
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____14046] in
                                                               uu____14042 ::
                                                                 uu____14043 in
                                                             uu____14038 ::
                                                               uu____14039 in
                                                           uu____14034 ::
                                                             uu____14035 in
                                                         uu____14030 ::
                                                           uu____14031 in
                                                       uu____14026 ::
                                                         uu____14027 in
                                                     (bind_inst, uu____14023) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____14008 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____14007 in
                                               uu____14004
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____14054 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____14054 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____14078 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____14078 with
                            | (uu____14079,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____14108 =
                                        let uu____14109 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____14109.FStar_Syntax_Syntax.n in
                                      match uu____14108 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____14115) -> t4
                                      | uu____14120 -> head2 in
                                    let uu____14121 =
                                      let uu____14122 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____14122.FStar_Syntax_Syntax.n in
                                    match uu____14121 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____14128 ->
                                        FStar_Pervasives_Native.None in
                                  let uu____14129 = maybe_extract_fv head2 in
                                  match uu____14129 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____14139 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____14139
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____14144 =
                                          maybe_extract_fv head3 in
                                        match uu____14144 with
                                        | FStar_Pervasives_Native.Some
                                            uu____14149 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____14150 ->
                                            FStar_Pervasives_Native.Some
                                              false in
                                      (head3, action_unfolded)
                                  | uu____14155 ->
                                      (head2, FStar_Pervasives_Native.None) in
                                ((let is_arg_impure uu____14170 =
                                    match uu____14170 with
                                    | (e,q) ->
                                        let uu____14177 =
                                          let uu____14178 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____14178.FStar_Syntax_Syntax.n in
                                        (match uu____14177 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____14193 -> false) in
                                  let uu____14194 =
                                    let uu____14195 =
                                      let uu____14202 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____14202 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____14195 in
                                  if uu____14194
                                  then
                                    let uu____14207 =
                                      let uu____14208 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____14208 in
                                    failwith uu____14207
                                  else ());
                                 (let uu____14210 =
                                    maybe_unfold_action head_app in
                                  match uu____14210 with
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
                                      let uu____14249 = FStar_List.tl stack1 in
                                      norm cfg env uu____14249 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____14263 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____14263 in
                           let uu____14264 = FStar_List.tl stack1 in
                           norm cfg env uu____14264 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____14385  ->
                                     match uu____14385 with
                                     | (pat,wopt,tm) ->
                                         let uu____14433 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____14433))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____14465 = FStar_List.tl stack1 in
                           norm cfg env uu____14465 tm
                       | uu____14466 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.pos = uu____14475;
                             FStar_Syntax_Syntax.vars = uu____14476;_},uu____14477,uu____14478))::uu____14479
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____14486 -> false in
                    if should_reify
                    then
                      let uu____14487 = FStar_List.tl stack1 in
                      let uu____14488 =
                        let uu____14489 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____14489 in
                      norm cfg env uu____14487 uu____14488
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____14492 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____14492
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___192_14501 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___192_14501.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___192_14501.primitive_steps)
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
                | uu____14503 ->
                    (match stack1 with
                     | uu____14504::uu____14505 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled
                              (l,r,uu____14510) ->
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
                          | uu____14535 -> norm cfg env stack1 head1)
                     | [] ->
                         let head2 = norm cfg env [] head1 in
                         let m1 =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               let uu____14549 =
                                 norm_pattern_args cfg env args in
                               FStar_Syntax_Syntax.Meta_pattern uu____14549
                           | uu____14560 -> m in
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
              let uu____14572 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____14572 with
              | (uu____14573,return_repr) ->
                  let return_inst =
                    let uu____14582 =
                      let uu____14583 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____14583.FStar_Syntax_Syntax.n in
                    match uu____14582 with
                    | FStar_Syntax_Syntax.Tm_uinst
                        (return_tm,uu____14589::[]) ->
                        let uu____14596 =
                          let uu____14599 =
                            let uu____14600 =
                              let uu____14607 =
                                let uu____14610 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____14610] in
                              (return_tm, uu____14607) in
                            FStar_Syntax_Syntax.Tm_uinst uu____14600 in
                          FStar_Syntax_Syntax.mk uu____14599 in
                        uu____14596 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____14618 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____14621 =
                    let uu____14624 =
                      let uu____14625 =
                        let uu____14640 =
                          let uu____14643 = FStar_Syntax_Syntax.as_arg t in
                          let uu____14644 =
                            let uu____14647 = FStar_Syntax_Syntax.as_arg e in
                            [uu____14647] in
                          uu____14643 :: uu____14644 in
                        (return_inst, uu____14640) in
                      FStar_Syntax_Syntax.Tm_app uu____14625 in
                    FStar_Syntax_Syntax.mk uu____14624 in
                  uu____14621 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____14656 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____14656 with
               | FStar_Pervasives_Native.None  ->
                   let uu____14659 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____14659
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____14660;
                     FStar_TypeChecker_Env.mtarget = uu____14661;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____14662;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____14673;
                     FStar_TypeChecker_Env.mtarget = uu____14674;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____14675;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____14693 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____14693)
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
                (fun uu____14749  ->
                   match uu____14749 with
                   | (a,imp) ->
                       let uu____14760 = norm cfg env [] a in
                       (uu____14760, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___193_14777 = comp1 in
            let uu____14780 =
              let uu____14781 =
                let uu____14790 = norm cfg env [] t in
                let uu____14791 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____14790, uu____14791) in
              FStar_Syntax_Syntax.Total uu____14781 in
            {
              FStar_Syntax_Syntax.n = uu____14780;
              FStar_Syntax_Syntax.pos =
                (uu___193_14777.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___193_14777.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___194_14806 = comp1 in
            let uu____14809 =
              let uu____14810 =
                let uu____14819 = norm cfg env [] t in
                let uu____14820 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____14819, uu____14820) in
              FStar_Syntax_Syntax.GTotal uu____14810 in
            {
              FStar_Syntax_Syntax.n = uu____14809;
              FStar_Syntax_Syntax.pos =
                (uu___194_14806.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___194_14806.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____14872  ->
                      match uu____14872 with
                      | (a,i) ->
                          let uu____14883 = norm cfg env [] a in
                          (uu____14883, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___147_14894  ->
                      match uu___147_14894 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____14898 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____14898
                      | f -> f)) in
            let uu___195_14902 = comp1 in
            let uu____14905 =
              let uu____14906 =
                let uu___196_14907 = ct in
                let uu____14908 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____14909 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____14912 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____14908;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___196_14907.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____14909;
                  FStar_Syntax_Syntax.effect_args = uu____14912;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____14906 in
            {
              FStar_Syntax_Syntax.n = uu____14905;
              FStar_Syntax_Syntax.pos =
                (uu___195_14902.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___195_14902.FStar_Syntax_Syntax.vars)
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
            (let uu___197_14930 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___197_14930.tcenv);
               delta_level = (uu___197_14930.delta_level);
               primitive_steps = (uu___197_14930.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____14935 = norm1 t in
          FStar_Syntax_Util.non_informative uu____14935 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____14938 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___198_14957 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.pos =
                (uu___198_14957.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___198_14957.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____14964 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____14964
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
                    let uu___199_14975 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___199_14975.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___199_14975.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___199_14975.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___200_14977 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___200_14977.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___200_14977.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___200_14977.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___200_14977.FStar_Syntax_Syntax.flags)
                    } in
              let uu___201_14978 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos =
                  (uu___201_14978.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___201_14978.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____14980 -> c
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____14983  ->
        match uu____14983 with
        | (x,imp) ->
            let uu____14986 =
              let uu___202_14987 = x in
              let uu____14988 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___202_14987.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___202_14987.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____14988
              } in
            (uu____14986, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____14994 =
          FStar_List.fold_left
            (fun uu____15012  ->
               fun b  ->
                 match uu____15012 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____14994 with | (nbs,uu____15040) -> FStar_List.rev nbs
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
            let uu____15056 =
              let uu___203_15057 = rc in
              let uu____15058 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___203_15057.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____15058;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___203_15057.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____15056
        | uu____15065 -> lopt
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
              ((let uu____15077 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____15077
                then
                  let uu____15078 = FStar_Syntax_Print.term_to_string tm in
                  let uu____15079 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2 "Normalized %s to %s\n" uu____15078
                    uu____15079
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___204_15097 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___204_15097.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____15166  ->
                    let uu____15167 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____15167);
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
              let uu____15203 =
                let uu___205_15204 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___205_15204.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___205_15204.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____15203
          | (Arg (Univ uu____15205,uu____15206,uu____15207))::uu____15208 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____15211,uu____15212))::uu____15213 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____15229),aq,r))::stack2 ->
              (log cfg
                 (fun uu____15258  ->
                    let uu____15259 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____15259);
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
                 (let uu____15269 = FStar_ST.read m in
                  match uu____15269 with
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
                  | FStar_Pervasives_Native.Some (uu____15369,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq)
                          FStar_Pervasives_Native.None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 =
                FStar_Syntax_Syntax.extend_app head1 (t, aq)
                  FStar_Pervasives_Native.None r in
              let uu____15393 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____15393
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____15403  ->
                    let uu____15404 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____15404);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____15409 =
                  log cfg
                    (fun uu____15414  ->
                       let uu____15415 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____15416 =
                         let uu____15417 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____15434  ->
                                   match uu____15434 with
                                   | (p,uu____15444,uu____15445) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____15417
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____15415 uu____15416);
                  (let whnf = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___148_15462  ->
                               match uu___148_15462 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____15463 -> false)) in
                     let steps' =
                       let uu____15467 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____15467
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___206_15471 = cfg in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___206_15471.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___206_15471.primitive_steps)
                     } in
                   let norm_or_whnf env2 t1 =
                     if whnf
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____15515 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____15538 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____15604  ->
                                   fun uu____15605  ->
                                     match (uu____15604, uu____15605) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____15708 = norm_pat env3 p1 in
                                         (match uu____15708 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____15538 with
                          | (pats1,env3) ->
                              ((let uu___207_15810 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.p =
                                    (uu___207_15810.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___208_15829 = x in
                           let uu____15830 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___208_15829.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___208_15829.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____15830
                           } in
                         ((let uu___209_15838 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.p =
                               (uu___209_15838.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___210_15843 = x in
                           let uu____15844 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___210_15843.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___210_15843.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____15844
                           } in
                         ((let uu___211_15852 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.p =
                               (uu___211_15852.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___212_15862 = x in
                           let uu____15863 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___212_15862.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___212_15862.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____15863
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___213_15872 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.p =
                               (uu___213_15872.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf -> branches
                     | uu____15876 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____15890 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____15890 with
                                 | (p,wopt,e) ->
                                     let uu____15910 = norm_pat env1 p in
                                     (match uu____15910 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Pervasives_Native.Some w
                                                ->
                                                let uu____15941 =
                                                  norm_or_whnf env2 w in
                                                FStar_Pervasives_Native.Some
                                                  uu____15941 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____15947 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____15947) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____15957) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____15962 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____15963;
                        FStar_Syntax_Syntax.fv_delta = uu____15964;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Data_ctor );_}
                      -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____15965;
                        FStar_Syntax_Syntax.fv_delta = uu____15966;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Record_ctor uu____15967);_}
                      -> true
                  | uu____15974 -> false in
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
                  let uu____16103 =
                    FStar_Syntax_Util.head_and_args scrutinee1 in
                  match uu____16103 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var uu____16152 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_wild uu____16155 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____16158 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee1.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____16177 ->
                                let uu____16178 =
                                  let uu____16179 = is_cons head1 in
                                  Prims.op_Negation uu____16179 in
                                FStar_Util.Inr uu____16178)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____16200 =
                             let uu____16201 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____16201.FStar_Syntax_Syntax.n in
                           (match uu____16200 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____16211 ->
                                let uu____16212 =
                                  let uu____16213 = is_cons head1 in
                                  Prims.op_Negation uu____16213 in
                                FStar_Util.Inr uu____16212))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____16266)::rest_a,(p1,uu____16269)::rest_p) ->
                      let uu____16313 = matches_pat t1 p1 in
                      (match uu____16313 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____16338 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____16440 = matches_pat scrutinee1 p1 in
                      (match uu____16440 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____16460  ->
                                 let uu____16461 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____16462 =
                                   let uu____16463 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____16463
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____16461 uu____16462);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____16480 =
                                        let uu____16481 =
                                          let uu____16500 =
                                            FStar_Util.mk_ref
                                              (FStar_Pervasives_Native.Some
                                                 ([], t1)) in
                                          ([], t1, uu____16500, false) in
                                        Clos uu____16481 in
                                      uu____16480 :: env2) env1 s in
                             let uu____16553 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____16553))) in
                let uu____16554 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____16554
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___149_16577  ->
                match uu___149_16577 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____16581 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____16587 -> d in
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
            let uu___214_16616 = config s e in
            {
              steps = (uu___214_16616.steps);
              tcenv = (uu___214_16616.tcenv);
              delta_level = (uu___214_16616.delta_level);
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
      fun t  -> let uu____16641 = config s e in norm_comp uu____16641 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____16650 = config [] env in norm_universe uu____16650 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let uu____16659 = config [] env in ghost_to_pure_aux uu____16659 [] c
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
        let uu____16673 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____16673 in
      let uu____16674 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____16674
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___215_16676 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___215_16676.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___215_16676.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____16679  ->
                    let uu____16680 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____16680))
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
            ((let uu____16699 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____16699);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____16712 = config [AllowUnboundUniverses] env in
          norm_comp uu____16712 [] c
        with
        | e ->
            ((let uu____16719 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____16719);
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
                   let uu____16759 =
                     let uu____16760 =
                       let uu____16767 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____16767) in
                     FStar_Syntax_Syntax.Tm_refine uu____16760 in
                   mk uu____16759 t01.FStar_Syntax_Syntax.pos
               | uu____16772 -> t2)
          | uu____16773 -> t2 in
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
        let uu____16825 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____16825 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____16854 ->
                 let uu____16861 = FStar_Syntax_Util.abs_formals e in
                 (match uu____16861 with
                  | (actuals,uu____16871,uu____16872) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____16886 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____16886 with
                         | (binders,args) ->
                             let uu____16903 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____16903
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
      | uu____16913 ->
          let uu____16914 = FStar_Syntax_Util.head_and_args t in
          (match uu____16914 with
           | (head1,args) ->
               let uu____16951 =
                 let uu____16952 = FStar_Syntax_Subst.compress head1 in
                 uu____16952.FStar_Syntax_Syntax.n in
               (match uu____16951 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____16955,thead) ->
                    let uu____16981 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____16981 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____17023 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___220_17031 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___220_17031.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___220_17031.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___220_17031.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___220_17031.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___220_17031.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___220_17031.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___220_17031.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___220_17031.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___220_17031.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___220_17031.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___220_17031.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___220_17031.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___220_17031.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___220_17031.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___220_17031.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___220_17031.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___220_17031.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___220_17031.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___220_17031.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___220_17031.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___220_17031.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___220_17031.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___220_17031.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___220_17031.FStar_TypeChecker_Env.is_native_tactic)
                                 }) t in
                            match uu____17023 with
                            | (uu____17032,ty,uu____17034) ->
                                eta_expand_with_type env t ty))
                | uu____17035 ->
                    let uu____17036 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___221_17044 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___221_17044.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___221_17044.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___221_17044.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___221_17044.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___221_17044.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___221_17044.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___221_17044.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___221_17044.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___221_17044.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___221_17044.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___221_17044.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___221_17044.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___221_17044.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___221_17044.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___221_17044.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___221_17044.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___221_17044.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___221_17044.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___221_17044.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___221_17044.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___221_17044.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___221_17044.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___221_17044.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___221_17044.FStar_TypeChecker_Env.is_native_tactic)
                         }) t in
                    (match uu____17036 with
                     | (uu____17045,ty,uu____17047) ->
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
            | (uu____17125,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____17131,FStar_Util.Inl t) ->
                let uu____17137 =
                  let uu____17140 =
                    let uu____17141 =
                      let uu____17154 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____17154) in
                    FStar_Syntax_Syntax.Tm_arrow uu____17141 in
                  FStar_Syntax_Syntax.mk uu____17140 in
                uu____17137 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____17158 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____17158 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____17185 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____17240 ->
                    let uu____17241 =
                      let uu____17250 =
                        let uu____17251 = FStar_Syntax_Subst.compress t3 in
                        uu____17251.FStar_Syntax_Syntax.n in
                      (uu____17250, tc) in
                    (match uu____17241 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____17276) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____17313) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____17352,FStar_Util.Inl uu____17353) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____17376 -> failwith "Impossible") in
              (match uu____17185 with
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
          let uu____17485 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____17485 with
          | (univ_names1,binders1,tc) ->
              let uu____17543 = FStar_Util.left tc in
              (univ_names1, binders1, uu____17543)
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
          let uu____17582 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____17582 with
          | (univ_names1,binders1,tc) ->
              let uu____17642 = FStar_Util.right tc in
              (univ_names1, binders1, uu____17642)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____17677 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____17677 with
           | (univ_names1,binders1,typ1) ->
               let uu___222_17705 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___222_17705.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___222_17705.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___222_17705.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___222_17705.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___223_17726 = s in
          let uu____17727 =
            let uu____17728 =
              let uu____17737 = FStar_List.map (elim_uvars env) sigs in
              (uu____17737, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____17728 in
          {
            FStar_Syntax_Syntax.sigel = uu____17727;
            FStar_Syntax_Syntax.sigrng =
              (uu___223_17726.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___223_17726.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___223_17726.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___223_17726.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____17754 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____17754 with
           | (univ_names1,uu____17772,typ1) ->
               let uu___224_17786 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___224_17786.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___224_17786.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___224_17786.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___224_17786.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____17792 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____17792 with
           | (univ_names1,uu____17810,typ1) ->
               let uu___225_17824 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___225_17824.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___225_17824.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___225_17824.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___225_17824.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____17858 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____17858 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____17881 =
                            let uu____17882 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____17882 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____17881 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___226_17885 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___226_17885.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___226_17885.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___227_17886 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___227_17886.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___227_17886.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___227_17886.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___227_17886.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___228_17898 = s in
          let uu____17899 =
            let uu____17900 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____17900 in
          {
            FStar_Syntax_Syntax.sigel = uu____17899;
            FStar_Syntax_Syntax.sigrng =
              (uu___228_17898.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___228_17898.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___228_17898.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___228_17898.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____17904 = elim_uvars_aux_t env us [] t in
          (match uu____17904 with
           | (us1,uu____17922,t1) ->
               let uu___229_17936 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___229_17936.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___229_17936.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___229_17936.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___229_17936.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____17937 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____17939 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____17939 with
           | (univs1,binders,signature) ->
               let uu____17967 =
                 let uu____17976 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____17976 with
                 | (univs_opening,univs2) ->
                     let uu____18003 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____18003) in
               (match uu____17967 with
                | (univs_opening,univs_closing) ->
                    let uu____18020 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____18026 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____18027 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____18026, uu____18027) in
                    (match uu____18020 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____18049 =
                           match uu____18049 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____18067 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____18067 with
                                | (us1,t1) ->
                                    let uu____18078 =
                                      let uu____18083 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____18090 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____18083, uu____18090) in
                                    (match uu____18078 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____18103 =
                                           let uu____18108 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____18117 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____18108, uu____18117) in
                                         (match uu____18103 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____18133 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____18133 in
                                              let uu____18134 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____18134 with
                                               | (uu____18155,uu____18156,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____18171 =
                                                       let uu____18172 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____18172 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____18171 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____18177 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____18177 with
                           | (uu____18190,uu____18191,t1) -> t1 in
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
                             | uu____18251 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____18268 =
                               let uu____18269 =
                                 FStar_Syntax_Subst.compress body in
                               uu____18269.FStar_Syntax_Syntax.n in
                             match uu____18268 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____18328 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____18357 =
                               let uu____18358 =
                                 FStar_Syntax_Subst.compress t in
                               uu____18358.FStar_Syntax_Syntax.n in
                             match uu____18357 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____18379) ->
                                 let uu____18400 = destruct_action_body body in
                                 (match uu____18400 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____18445 ->
                                 let uu____18446 = destruct_action_body t in
                                 (match uu____18446 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____18495 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____18495 with
                           | (action_univs,t) ->
                               let uu____18504 = destruct_action_typ_templ t in
                               (match uu____18504 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___230_18545 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___230_18545.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___230_18545.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___231_18547 = ed in
                           let uu____18548 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____18549 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____18550 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____18551 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____18552 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____18553 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____18554 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____18555 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____18556 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____18557 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____18558 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____18559 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____18560 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____18561 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___231_18547.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___231_18547.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____18548;
                             FStar_Syntax_Syntax.bind_wp = uu____18549;
                             FStar_Syntax_Syntax.if_then_else = uu____18550;
                             FStar_Syntax_Syntax.ite_wp = uu____18551;
                             FStar_Syntax_Syntax.stronger = uu____18552;
                             FStar_Syntax_Syntax.close_wp = uu____18553;
                             FStar_Syntax_Syntax.assert_p = uu____18554;
                             FStar_Syntax_Syntax.assume_p = uu____18555;
                             FStar_Syntax_Syntax.null_wp = uu____18556;
                             FStar_Syntax_Syntax.trivial = uu____18557;
                             FStar_Syntax_Syntax.repr = uu____18558;
                             FStar_Syntax_Syntax.return_repr = uu____18559;
                             FStar_Syntax_Syntax.bind_repr = uu____18560;
                             FStar_Syntax_Syntax.actions = uu____18561
                           } in
                         let uu___232_18564 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___232_18564.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___232_18564.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___232_18564.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___232_18564.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___150_18581 =
            match uu___150_18581 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____18608 = elim_uvars_aux_t env us [] t in
                (match uu____18608 with
                 | (us1,uu____18632,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___233_18651 = sub_eff in
            let uu____18652 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____18655 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___233_18651.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___233_18651.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____18652;
              FStar_Syntax_Syntax.lift = uu____18655
            } in
          let uu___234_18658 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___234_18658.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___234_18658.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___234_18658.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___234_18658.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____18668 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____18668 with
           | (univ_names1,binders1,comp1) ->
               let uu___235_18702 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___235_18702.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___235_18702.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___235_18702.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___235_18702.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____18713 -> s