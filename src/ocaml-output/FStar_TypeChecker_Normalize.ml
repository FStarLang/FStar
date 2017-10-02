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
  | Unmeta[@@deriving show]
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
let uu___is_Unmeta: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____154 -> false
type steps = step Prims.list[@@deriving show]
type primitive_step =
  {
  name: FStar_Ident.lid;
  arity: Prims.int;
  strong_reduction_ok: Prims.bool;
  interpretation:
    FStar_Range.range ->
      FStar_Syntax_Syntax.args ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option;}[@@deriving
                                                                   show]
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
  | Dummy[@@deriving show]
let uu___is_Clos: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Clos _0 -> true | uu____308 -> false
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
    match projectee with | Univ _0 -> true | uu____376 -> false
let __proj__Univ__item___0: closure -> FStar_Syntax_Syntax.universe =
  fun projectee  -> match projectee with | Univ _0 -> _0
let uu___is_Dummy: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____389 -> false
type env = closure Prims.list[@@deriving show]
let closure_to_string: closure -> Prims.string =
  fun uu___168_395  ->
    match uu___168_395 with
    | Clos (uu____396,t,uu____398,uu____399) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____420 -> "Univ"
    | Dummy  -> "dummy"
type cfg =
  {
  steps: steps;
  tcenv: FStar_TypeChecker_Env.env;
  delta_level: FStar_TypeChecker_Env.delta_level Prims.list;
  primitive_steps: primitive_step Prims.list;}[@@deriving show]
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
    FStar_Pervasives_Native.tuple3 Prims.list[@@deriving show]
type subst_t = FStar_Syntax_Syntax.subst_elt Prims.list[@@deriving show]
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
  FStar_Pervasives_Native.tuple2[@@deriving show]
let uu___is_Arg: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Arg _0 -> true | uu____641 -> false
let __proj__Arg__item___0:
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Arg _0 -> _0
let uu___is_UnivArgs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____679 -> false
let __proj__UnivArgs__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____717 -> false
let __proj__MemoLazy__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0
let uu___is_Match: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____776 -> false
let __proj__Match__item___0:
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Abs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____820 -> false
let __proj__Abs__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____876 -> false
let __proj__App__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Meta: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____912 -> false
let __proj__Meta__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Meta _0 -> _0
let uu___is_Let: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____946 -> false
let __proj__Let__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Steps: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Steps _0 -> true | uu____994 -> false
let __proj__Steps__item___0:
  stack_elt ->
    (steps,primitive_step Prims.list,FStar_TypeChecker_Env.delta_level
                                       Prims.list)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Steps _0 -> _0
let uu___is_Debug: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____1042 -> false
let __proj__Debug__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list[@@deriving show]
let mk:
  'Auu____1071 .
    'Auu____1071 ->
      FStar_Range.range -> 'Auu____1071 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r
let set_memo:
  'Auu____1228 'Auu____1229 .
    ('Auu____1229 FStar_Pervasives_Native.option,'Auu____1228) FStar_ST.mref
      -> 'Auu____1229 -> Prims.unit
  =
  fun r  ->
    fun t  ->
      let uu____1524 = FStar_ST.op_Bang r in
      match uu____1524 with
      | FStar_Pervasives_Native.Some uu____1625 ->
          failwith "Unexpected set_memo: thunk already evaluated"
      | FStar_Pervasives_Native.None  ->
          FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____1732 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____1732 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___169_1740  ->
    match uu___169_1740 with
    | Arg (c,uu____1742,uu____1743) ->
        let uu____1744 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____1744
    | MemoLazy uu____1745 -> "MemoLazy"
    | Abs (uu____1752,bs,uu____1754,uu____1755,uu____1756) ->
        let uu____1761 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____1761
    | UnivArgs uu____1766 -> "UnivArgs"
    | Match uu____1773 -> "Match"
    | App (t,uu____1781,uu____1782) ->
        let uu____1783 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____1783
    | Meta (m,uu____1785) -> "Meta"
    | Let uu____1786 -> "Let"
    | Steps (uu____1795,uu____1796,uu____1797) -> "Steps"
    | Debug (t,uu____1807) ->
        let uu____1808 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____1808
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____1817 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____1817 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1835 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____1835 then f () else ()
let is_empty: 'Auu____1841 . 'Auu____1841 Prims.list -> Prims.bool =
  fun uu___170_1847  ->
    match uu___170_1847 with | [] -> true | uu____1850 -> false
let lookup_bvar:
  'Auu____1859 .
    'Auu____1859 Prims.list -> FStar_Syntax_Syntax.bv -> 'Auu____1859
  =
  fun env  ->
    fun x  ->
      try FStar_List.nth env x.FStar_Syntax_Syntax.index
      with
      | uu____1878 ->
          let uu____1879 =
            let uu____1880 = FStar_Syntax_Print.db_to_string x in
            FStar_Util.format1 "Failed to find %s\n" uu____1880 in
          failwith uu____1879
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
          let uu____1925 =
            FStar_List.fold_left
              (fun uu____1951  ->
                 fun u1  ->
                   match uu____1951 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____1976 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____1976 with
                        | (k_u,n1) ->
                            let uu____1991 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____1991
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____1925 with
          | (uu____2009,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____2034 = FStar_List.nth env x in
                 match uu____2034 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____2038 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____2047 ->
                   let uu____2048 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____2048
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____2054 when
              FStar_All.pipe_right cfg.steps
                (FStar_List.contains CheckNoUvars)
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____2063 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____2072 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____2079 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____2079 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____2096 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____2096 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____2104 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____2112 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____2112 with
                                  | (uu____2117,m) -> n1 <= m)) in
                        if uu____2104 then rest1 else us1
                    | uu____2122 -> us1)
               | uu____2127 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____2131 = aux u3 in
              FStar_List.map (fun _0_42  -> FStar_Syntax_Syntax.U_succ _0_42)
                uu____2131 in
        let uu____2134 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____2134
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____2136 = aux u in
           match uu____2136 with
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
          (fun uu____2256  ->
             let uu____2257 = FStar_Syntax_Print.tag_of_term t in
             let uu____2258 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____2257
               uu____2258);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____2259 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____2263 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____2288 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____2289 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____2290 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____2291 ->
                  let uu____2308 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains CheckNoUvars) in
                  if uu____2308
                  then
                    let uu____2309 =
                      let uu____2310 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos in
                      let uu____2311 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____2310 uu____2311 in
                    failwith uu____2309
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____2314 =
                    let uu____2315 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____2315 in
                  mk uu____2314 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____2322 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____2322
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____2324 = lookup_bvar env x in
                  (match uu____2324 with
                   | Univ uu____2325 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____2329) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____2417 = closures_as_binders_delayed cfg env bs in
                  (match uu____2417 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____2451 =
                         let uu____2452 =
                           let uu____2469 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____2469) in
                         FStar_Syntax_Syntax.Tm_abs uu____2452 in
                       mk uu____2451 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____2500 = closures_as_binders_delayed cfg env bs in
                  (match uu____2500 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____2548 =
                    let uu____2561 =
                      let uu____2568 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____2568] in
                    closures_as_binders_delayed cfg env uu____2561 in
                  (match uu____2548 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____2590 =
                         let uu____2591 =
                           let uu____2598 =
                             let uu____2599 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____2599
                               FStar_Pervasives_Native.fst in
                           (uu____2598, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____2591 in
                       mk uu____2590 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____2690 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____2690
                    | FStar_Util.Inr c ->
                        let uu____2704 = close_comp cfg env c in
                        FStar_Util.Inr uu____2704 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____2720 =
                    let uu____2721 =
                      let uu____2748 = closure_as_term_delayed cfg env t11 in
                      (uu____2748, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____2721 in
                  mk uu____2720 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____2799 =
                    let uu____2800 =
                      let uu____2807 = closure_as_term_delayed cfg env t' in
                      let uu____2810 =
                        let uu____2811 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____2811 in
                      (uu____2807, uu____2810) in
                    FStar_Syntax_Syntax.Tm_meta uu____2800 in
                  mk uu____2799 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____2871 =
                    let uu____2872 =
                      let uu____2879 = closure_as_term_delayed cfg env t' in
                      let uu____2882 =
                        let uu____2883 =
                          let uu____2890 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____2890) in
                        FStar_Syntax_Syntax.Meta_monadic uu____2883 in
                      (uu____2879, uu____2882) in
                    FStar_Syntax_Syntax.Tm_meta uu____2872 in
                  mk uu____2871 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____2909 =
                    let uu____2910 =
                      let uu____2917 = closure_as_term_delayed cfg env t' in
                      let uu____2920 =
                        let uu____2921 =
                          let uu____2930 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____2930) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____2921 in
                      (uu____2917, uu____2920) in
                    FStar_Syntax_Syntax.Tm_meta uu____2910 in
                  mk uu____2909 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____2943 =
                    let uu____2944 =
                      let uu____2951 = closure_as_term_delayed cfg env t' in
                      (uu____2951, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____2944 in
                  mk uu____2943 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____2981  -> Dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let uu____2988 =
                    let uu____2999 = FStar_Syntax_Syntax.is_top_level [lb] in
                    if uu____2999
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       let uu____3018 =
                         closure_as_term cfg (Dummy :: env0) body in
                       ((FStar_Util.Inl
                           (let uu___188_3024 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___188_3024.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___188_3024.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____3018)) in
                  (match uu____2988 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___189_3040 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___189_3040.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___189_3040.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         } in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____3051,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____3086  -> fun env2  -> Dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____3093 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____3093
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____3101  -> fun env2  -> Dummy :: env2) lbs
                          env_univs in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let nm =
                      let uu____3111 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____3111
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         FStar_All.pipe_right
                           (let uu___190_3123 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___190_3123.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___190_3123.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_43  -> FStar_Util.Inl _0_43)) in
                    let uu___191_3124 = lb in
                    let uu____3125 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___191_3124.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___191_3124.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____3125
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____3143  -> fun env1  -> Dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____3222 =
                    match uu____3222 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____3287 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____3310 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____3376  ->
                                        fun uu____3377  ->
                                          match (uu____3376, uu____3377) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____3480 =
                                                norm_pat env3 p1 in
                                              (match uu____3480 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____3310 with
                               | (pats1,env3) ->
                                   ((let uu___192_3582 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___192_3582.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___193_3601 = x in
                                let uu____3602 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___193_3601.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___193_3601.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3602
                                } in
                              ((let uu___194_3610 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___194_3610.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___195_3615 = x in
                                let uu____3616 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___195_3615.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___195_3615.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3616
                                } in
                              ((let uu___196_3624 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___196_3624.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___197_3634 = x in
                                let uu____3635 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___197_3634.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___197_3634.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3635
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___198_3644 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___198_3644.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____3647 = norm_pat env1 pat in
                        (match uu____3647 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3682 =
                                     closure_as_term cfg env2 w in
                                   FStar_Pervasives_Native.Some uu____3682 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____3688 =
                    let uu____3689 =
                      let uu____3712 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____3712) in
                    FStar_Syntax_Syntax.Tm_match uu____3689 in
                  mk uu____3688 t1.FStar_Syntax_Syntax.pos))
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
        | uu____3794 -> closure_as_term cfg env t
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
        | uu____3818 ->
            FStar_List.map
              (fun uu____3837  ->
                 match uu____3837 with
                 | (x,imp) ->
                     let uu____3856 = closure_as_term_delayed cfg env x in
                     (uu____3856, imp)) args
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
        let uu____3872 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____3927  ->
                  fun uu____3928  ->
                    match (uu____3927, uu____3928) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___199_4010 = b in
                          let uu____4011 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___199_4010.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___199_4010.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____4011
                          } in
                        let env2 = Dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____3872 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____4092 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____4107 = closure_as_term_delayed cfg env t in
                 let uu____4108 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____4107 uu____4108
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____4121 = closure_as_term_delayed cfg env t in
                 let uu____4122 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____4121 uu____4122
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
                        (fun uu___171_4148  ->
                           match uu___171_4148 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____4152 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____4152
                           | f -> f)) in
                 let uu____4156 =
                   let uu___200_4157 = c1 in
                   let uu____4158 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____4158;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___200_4157.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____4156)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags  ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___172_4168  ->
            match uu___172_4168 with
            | FStar_Syntax_Syntax.DECREASES uu____4169 -> false
            | uu____4172 -> true))
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
                   (fun uu___173_4192  ->
                      match uu___173_4192 with
                      | FStar_Syntax_Syntax.DECREASES uu____4193 -> false
                      | uu____4196 -> true)) in
            let rc1 =
              let uu___201_4198 = rc in
              let uu____4199 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___201_4198.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____4199;
                FStar_Syntax_Syntax.residual_flags = flags
              } in
            FStar_Pervasives_Native.Some rc1
        | uu____4206 -> lopt
let built_in_primitive_steps: primitive_step Prims.list =
  let const_as_tm c p = mk (FStar_Syntax_Syntax.Tm_constant c) p in
  let int_as_const p i =
    let uu____4227 =
      let uu____4228 =
        let uu____4239 = FStar_Util.string_of_int i in
        (uu____4239, FStar_Pervasives_Native.None) in
      FStar_Const.Const_int uu____4228 in
    const_as_tm uu____4227 p in
  let bool_as_const p b = const_as_tm (FStar_Const.Const_bool b) p in
  let string_as_const p b = const_as_tm (FStar_Const.Const_string (b, p)) p in
  let arg_as_int uu____4273 =
    match uu____4273 with
    | (a,uu____4281) ->
        let uu____4284 =
          let uu____4285 = FStar_Syntax_Subst.compress a in
          uu____4285.FStar_Syntax_Syntax.n in
        (match uu____4284 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (i,FStar_Pervasives_Native.None )) ->
             let uu____4301 = FStar_Util.int_of_string i in
             FStar_Pervasives_Native.Some uu____4301
         | uu____4302 -> FStar_Pervasives_Native.None) in
  let arg_as_bounded_int uu____4316 =
    match uu____4316 with
    | (a,uu____4328) ->
        let uu____4335 =
          let uu____4336 = FStar_Syntax_Subst.compress a in
          uu____4336.FStar_Syntax_Syntax.n in
        (match uu____4335 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____4346;
                FStar_Syntax_Syntax.vars = uu____4347;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____4349;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____4350;_},uu____4351)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____4390 =
               let uu____4395 = FStar_Util.int_of_string i in
               (fv1, uu____4395) in
             FStar_Pervasives_Native.Some uu____4390
         | uu____4400 -> FStar_Pervasives_Native.None) in
  let arg_as_bool uu____4414 =
    match uu____4414 with
    | (a,uu____4422) ->
        let uu____4425 =
          let uu____4426 = FStar_Syntax_Subst.compress a in
          uu____4426.FStar_Syntax_Syntax.n in
        (match uu____4425 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
             FStar_Pervasives_Native.Some b
         | uu____4432 -> FStar_Pervasives_Native.None) in
  let arg_as_char uu____4442 =
    match uu____4442 with
    | (a,uu____4450) ->
        let uu____4453 =
          let uu____4454 = FStar_Syntax_Subst.compress a in
          uu____4454.FStar_Syntax_Syntax.n in
        (match uu____4453 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
             FStar_Pervasives_Native.Some c
         | uu____4460 -> FStar_Pervasives_Native.None) in
  let arg_as_string uu____4470 =
    match uu____4470 with
    | (a,uu____4478) ->
        let uu____4481 =
          let uu____4482 = FStar_Syntax_Subst.compress a in
          uu____4482.FStar_Syntax_Syntax.n in
        (match uu____4481 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____4488)) -> FStar_Pervasives_Native.Some s
         | uu____4489 -> FStar_Pervasives_Native.None) in
  let arg_as_list f uu____4515 =
    match uu____4515 with
    | (a,uu____4529) ->
        let rec sequence l =
          match l with
          | [] -> FStar_Pervasives_Native.Some []
          | (FStar_Pervasives_Native.None )::uu____4558 ->
              FStar_Pervasives_Native.None
          | (FStar_Pervasives_Native.Some x)::xs ->
              let uu____4575 = sequence xs in
              (match uu____4575 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some xs' ->
                   FStar_Pervasives_Native.Some (x :: xs')) in
        let uu____4595 = FStar_Syntax_Util.list_elements a in
        (match uu____4595 with
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some elts ->
             let uu____4613 =
               FStar_List.map
                 (fun x  ->
                    let uu____4623 = FStar_Syntax_Syntax.as_arg x in
                    f uu____4623) elts in
             sequence uu____4613) in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4661 = f a in FStar_Pervasives_Native.Some uu____4661
    | uu____4662 -> FStar_Pervasives_Native.None in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4712 = f a0 a1 in FStar_Pervasives_Native.Some uu____4712
    | uu____4713 -> FStar_Pervasives_Native.None in
  let unary_op as_a f r args =
    let uu____4762 = FStar_List.map as_a args in lift_unary (f r) uu____4762 in
  let binary_op as_a f r args =
    let uu____4818 = FStar_List.map as_a args in lift_binary (f r) uu____4818 in
  let as_primitive_step uu____4842 =
    match uu____4842 with
    | (l,arity,f) ->
        { name = l; arity; strong_reduction_ok = true; interpretation = f } in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  -> fun x  -> let uu____4890 = f x in int_as_const r uu____4890) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  -> let uu____4918 = f x y in int_as_const r uu____4918) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  -> fun x  -> let uu____4939 = f x in bool_as_const r uu____4939) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  -> let uu____4967 = f x y in bool_as_const r uu____4967) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  -> let uu____4995 = f x y in string_as_const r uu____4995) in
  let list_of_string' rng s =
    let name l =
      let uu____5009 =
        let uu____5010 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____5010 in
      mk uu____5009 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____5020 =
      let uu____5023 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____5023 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____5020 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in int_as_const rng r in
  let string_concat' rng args =
    match args with
    | a1::a2::[] ->
        let uu____5098 = arg_as_string a1 in
        (match uu____5098 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5104 = arg_as_list arg_as_string a2 in
             (match uu____5104 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____5117 = string_as_const rng r in
                  FStar_Pervasives_Native.Some uu____5117
              | uu____5118 -> FStar_Pervasives_Native.None)
         | uu____5123 -> FStar_Pervasives_Native.None)
    | uu____5126 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____5140 = FStar_Util.string_of_int i in
    string_as_const rng uu____5140 in
  let string_of_bool1 rng b =
    string_as_const rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____5156 = FStar_Util.string_of_int i in
    string_as_const rng uu____5156 in
  let string_of_bool2 rng b =
    string_as_const rng (if b then "true" else "false") in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r in
  let range_of1 uu____5186 args =
    match args with
    | uu____5198::(t,uu____5200)::[] ->
        let uu____5229 = term_of_range t.FStar_Syntax_Syntax.pos in
        FStar_Pervasives_Native.Some uu____5229
    | uu____5234 -> FStar_Pervasives_Native.None in
  let set_range_of1 r args =
    match args with
    | uu____5266::(t,uu____5268)::(r1,uu____5270)::[] ->
        let r2 = FStar_Syntax_Embeddings.unembed_range r1 in
        FStar_Pervasives_Native.Some
          (let uu___202_5295 = t in
           {
             FStar_Syntax_Syntax.n = (uu___202_5295.FStar_Syntax_Syntax.n);
             FStar_Syntax_Syntax.pos = r2;
             FStar_Syntax_Syntax.vars =
               (uu___202_5295.FStar_Syntax_Syntax.vars)
           })
    | uu____5296 -> FStar_Pervasives_Native.None in
  let mk_range1 r args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____5375 =
          let uu____5396 = arg_as_string fn in
          let uu____5399 = arg_as_int from_line in
          let uu____5402 = arg_as_int from_col in
          let uu____5405 = arg_as_int to_line in
          let uu____5408 = arg_as_int to_col in
          (uu____5396, uu____5399, uu____5402, uu____5405, uu____5408) in
        (match uu____5375 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r1 =
               let uu____5439 = FStar_Range.mk_pos from_l from_c in
               let uu____5440 = FStar_Range.mk_pos to_l to_c in
               FStar_Range.mk_range fn1 uu____5439 uu____5440 in
             let uu____5441 = term_of_range r1 in
             FStar_Pervasives_Native.Some uu____5441
         | uu____5446 -> FStar_Pervasives_Native.None)
    | uu____5467 -> FStar_Pervasives_Native.None in
  let decidable_eq neg rng args =
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) rng in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) rng in
    match args with
    | (_typ,uu____5497)::(a1,uu____5499)::(a2,uu____5501)::[] ->
        let uu____5538 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____5538 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____5551 -> FStar_Pervasives_Native.None)
    | uu____5552 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____5570 =
      let uu____5585 =
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
                                              let uu____5883 =
                                                FStar_Parser_Const.p2l
                                                  ["FStar";
                                                  "String";
                                                  "list_of_string"] in
                                              (uu____5883,
                                                (Prims.parse_int "1"),
                                                (unary_op arg_as_string
                                                   list_of_string')) in
                                            let uu____5890 =
                                              let uu____5905 =
                                                let uu____5918 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "string_of_list"] in
                                                (uu____5918,
                                                  (Prims.parse_int "1"),
                                                  (unary_op
                                                     (arg_as_list arg_as_char)
                                                     string_of_list')) in
                                              let uu____5927 =
                                                let uu____5942 =
                                                  let uu____5961 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "concat"] in
                                                  (uu____5961,
                                                    (Prims.parse_int "2"),
                                                    string_concat') in
                                                let uu____5974 =
                                                  let uu____5995 =
                                                    let uu____6016 =
                                                      FStar_Parser_Const.p2l
                                                        ["Prims"; "range_of"] in
                                                    (uu____6016,
                                                      (Prims.parse_int "2"),
                                                      range_of1) in
                                                  let uu____6031 =
                                                    let uu____6054 =
                                                      let uu____6073 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "set_range_of"] in
                                                      (uu____6073,
                                                        (Prims.parse_int "3"),
                                                        set_range_of1) in
                                                    let uu____6086 =
                                                      let uu____6107 =
                                                        let uu____6126 =
                                                          FStar_Parser_Const.p2l
                                                            ["Prims";
                                                            "mk_range"] in
                                                        (uu____6126,
                                                          (Prims.parse_int
                                                             "5"), mk_range1) in
                                                      [uu____6107] in
                                                    uu____6054 :: uu____6086 in
                                                  uu____5995 :: uu____6031 in
                                                uu____5942 :: uu____5974 in
                                              uu____5905 :: uu____5927 in
                                            uu____5870 :: uu____5890 in
                                          (FStar_Parser_Const.op_notEq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq true)) ::
                                            uu____5855 in
                                        (FStar_Parser_Const.op_Eq,
                                          (Prims.parse_int "3"),
                                          (decidable_eq false)) :: uu____5840 in
                                      (FStar_Parser_Const.string_compare,
                                        (Prims.parse_int "2"),
                                        (binary_op arg_as_string
                                           string_compare'))
                                        :: uu____5825 in
                                    (FStar_Parser_Const.string_of_bool_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_bool string_of_bool2))
                                      :: uu____5810 in
                                  (FStar_Parser_Const.string_of_int_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_int string_of_int2)) ::
                                    uu____5795 in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____5780 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5765 in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____5750 in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____5735 in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____5720 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____5705 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
                      :: uu____5690 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____5675 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____5660 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____5645 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____5630 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____5615 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____5600 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____5585 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____5570 in
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
      let uu____6731 =
        let uu____6732 =
          let uu____6733 = FStar_Syntax_Syntax.as_arg c in [uu____6733] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6732 in
      uu____6731 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____6768 =
              let uu____6781 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____6781, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____6800  ->
                        fun uu____6801  ->
                          match (uu____6800, uu____6801) with
                          | ((int_to_t1,x),(uu____6820,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____6830 =
              let uu____6845 =
                let uu____6858 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____6858, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____6877  ->
                          fun uu____6878  ->
                            match (uu____6877, uu____6878) with
                            | ((int_to_t1,x),(uu____6897,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____6907 =
                let uu____6922 =
                  let uu____6935 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____6935, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____6954  ->
                            fun uu____6955  ->
                              match (uu____6954, uu____6955) with
                              | ((int_to_t1,x),(uu____6974,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____6922] in
              uu____6845 :: uu____6907 in
            uu____6768 :: uu____6830)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop r args =
    match args with
    | (_typ,uu____7070)::(a1,uu____7072)::(a2,uu____7074)::[] ->
        let uu____7111 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____7111 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___203_7117 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___203_7117.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___203_7117.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___204_7121 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___204_7121.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___204_7121.FStar_Syntax_Syntax.vars)
                })
         | uu____7122 -> FStar_Pervasives_Native.None)
    | (_typ,uu____7124)::uu____7125::(a1,uu____7127)::(a2,uu____7129)::[] ->
        let uu____7178 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____7178 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___203_7184 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___203_7184.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___203_7184.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___204_7188 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___204_7188.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___204_7188.FStar_Syntax_Syntax.vars)
                })
         | uu____7189 -> FStar_Pervasives_Native.None)
    | uu____7190 -> failwith "Unexpected number of arguments" in
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
      let uu____7203 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops cfg.steps) in
      if uu____7203
      then tm
      else
        (let uu____7205 = FStar_Syntax_Util.head_and_args tm in
         match uu____7205 with
         | (head1,args) ->
             let uu____7242 =
               let uu____7243 = FStar_Syntax_Util.un_uinst head1 in
               uu____7243.FStar_Syntax_Syntax.n in
             (match uu____7242 with
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____7247 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps in
                  (match uu____7247 with
                   | FStar_Pervasives_Native.None  -> tm
                   | FStar_Pervasives_Native.Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then tm
                       else
                         (let uu____7260 =
                            prim_step.interpretation
                              head1.FStar_Syntax_Syntax.pos args in
                          match uu____7260 with
                          | FStar_Pervasives_Native.None  -> tm
                          | FStar_Pervasives_Native.Some reduced -> reduced))
              | uu____7264 -> tm))
let reduce_equality:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___205_7275 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___205_7275.tcenv);
           delta_level = (uu___205_7275.delta_level);
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
        let uu___206_7299 = t in
        {
          FStar_Syntax_Syntax.n = (uu___206_7299.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___206_7299.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid ->
            FStar_Pervasives_Native.Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid ->
            FStar_Pervasives_Native.Some false
        | uu____7316 -> FStar_Pervasives_Native.None in
      let simplify1 arg = ((simp_t (FStar_Pervasives_Native.fst arg)), arg) in
      let tm1 = reduce_primops cfg tm in
      let uu____7356 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps) in
      if uu____7356
      then tm1
      else
        (match tm1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.pos = uu____7359;
                     FStar_Syntax_Syntax.vars = uu____7360;_},uu____7361);
                FStar_Syntax_Syntax.pos = uu____7362;
                FStar_Syntax_Syntax.vars = uu____7363;_},args)
             ->
             let uu____7389 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
             if uu____7389
             then
               let uu____7390 =
                 FStar_All.pipe_right args (FStar_List.map simplify1) in
               (match uu____7390 with
                | (FStar_Pervasives_Native.Some (true ),uu____7445)::
                    (uu____7446,(arg,uu____7448))::[] -> arg
                | (uu____7513,(arg,uu____7515))::(FStar_Pervasives_Native.Some
                                                  (true ),uu____7516)::[]
                    -> arg
                | (FStar_Pervasives_Native.Some (false ),uu____7581)::uu____7582::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____7645::(FStar_Pervasives_Native.Some (false
                               ),uu____7646)::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____7709 -> tm1)
             else
               (let uu____7725 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
                if uu____7725
                then
                  let uu____7726 =
                    FStar_All.pipe_right args (FStar_List.map simplify1) in
                  match uu____7726 with
                  | (FStar_Pervasives_Native.Some (true ),uu____7781)::uu____7782::[]
                      -> w FStar_Syntax_Util.t_true
                  | uu____7845::(FStar_Pervasives_Native.Some (true
                                 ),uu____7846)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____7909)::
                      (uu____7910,(arg,uu____7912))::[] -> arg
                  | (uu____7977,(arg,uu____7979))::(FStar_Pervasives_Native.Some
                                                    (false ),uu____7980)::[]
                      -> arg
                  | uu____8045 -> tm1
                else
                  (let uu____8061 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.imp_lid in
                   if uu____8061
                   then
                     let uu____8062 =
                       FStar_All.pipe_right args (FStar_List.map simplify1) in
                     match uu____8062 with
                     | uu____8117::(FStar_Pervasives_Native.Some (true
                                    ),uu____8118)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____8181)::uu____8182::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____8245)::
                         (uu____8246,(arg,uu____8248))::[] -> arg
                     | (uu____8313,(p,uu____8315))::(uu____8316,(q,uu____8318))::[]
                         ->
                         let uu____8383 = FStar_Syntax_Util.term_eq p q in
                         (if uu____8383
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____8385 -> tm1
                   else
                     (let uu____8401 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____8401
                      then
                        let uu____8402 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1) in
                        match uu____8402 with
                        | (FStar_Pervasives_Native.Some (true ),uu____8457)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____8496)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____8535 -> tm1
                      else
                        (let uu____8551 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____8551
                         then
                           match args with
                           | (t,uu____8553)::[] ->
                               let uu____8570 =
                                 let uu____8571 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____8571.FStar_Syntax_Syntax.n in
                               (match uu____8570 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____8574::[],body,uu____8576) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____8603 -> tm1)
                                | uu____8606 -> tm1)
                           | (uu____8607,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____8608))::
                               (t,uu____8610)::[] ->
                               let uu____8649 =
                                 let uu____8650 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____8650.FStar_Syntax_Syntax.n in
                               (match uu____8649 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____8653::[],body,uu____8655) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____8682 -> tm1)
                                | uu____8685 -> tm1)
                           | uu____8686 -> tm1
                         else
                           (let uu____8696 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____8696
                            then
                              match args with
                              | (t,uu____8698)::[] ->
                                  let uu____8715 =
                                    let uu____8716 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____8716.FStar_Syntax_Syntax.n in
                                  (match uu____8715 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____8719::[],body,uu____8721) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____8748 -> tm1)
                                   | uu____8751 -> tm1)
                              | (uu____8752,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____8753))::
                                  (t,uu____8755)::[] ->
                                  let uu____8794 =
                                    let uu____8795 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____8795.FStar_Syntax_Syntax.n in
                                  (match uu____8794 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____8798::[],body,uu____8800) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____8827 -> tm1)
                                   | uu____8830 -> tm1)
                              | uu____8831 -> tm1
                            else reduce_equality cfg tm1)))))
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                FStar_Syntax_Syntax.pos = uu____8842;
                FStar_Syntax_Syntax.vars = uu____8843;_},args)
             ->
             let uu____8865 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
             if uu____8865
             then
               let uu____8866 =
                 FStar_All.pipe_right args (FStar_List.map simplify1) in
               (match uu____8866 with
                | (FStar_Pervasives_Native.Some (true ),uu____8921)::
                    (uu____8922,(arg,uu____8924))::[] -> arg
                | (uu____8989,(arg,uu____8991))::(FStar_Pervasives_Native.Some
                                                  (true ),uu____8992)::[]
                    -> arg
                | (FStar_Pervasives_Native.Some (false ),uu____9057)::uu____9058::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____9121::(FStar_Pervasives_Native.Some (false
                               ),uu____9122)::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____9185 -> tm1)
             else
               (let uu____9201 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
                if uu____9201
                then
                  let uu____9202 =
                    FStar_All.pipe_right args (FStar_List.map simplify1) in
                  match uu____9202 with
                  | (FStar_Pervasives_Native.Some (true ),uu____9257)::uu____9258::[]
                      -> w FStar_Syntax_Util.t_true
                  | uu____9321::(FStar_Pervasives_Native.Some (true
                                 ),uu____9322)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____9385)::
                      (uu____9386,(arg,uu____9388))::[] -> arg
                  | (uu____9453,(arg,uu____9455))::(FStar_Pervasives_Native.Some
                                                    (false ),uu____9456)::[]
                      -> arg
                  | uu____9521 -> tm1
                else
                  (let uu____9537 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.imp_lid in
                   if uu____9537
                   then
                     let uu____9538 =
                       FStar_All.pipe_right args (FStar_List.map simplify1) in
                     match uu____9538 with
                     | uu____9593::(FStar_Pervasives_Native.Some (true
                                    ),uu____9594)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____9657)::uu____9658::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____9721)::
                         (uu____9722,(arg,uu____9724))::[] -> arg
                     | (uu____9789,(p,uu____9791))::(uu____9792,(q,uu____9794))::[]
                         ->
                         let uu____9859 = FStar_Syntax_Util.term_eq p q in
                         (if uu____9859
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____9861 -> tm1
                   else
                     (let uu____9877 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____9877
                      then
                        let uu____9878 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1) in
                        match uu____9878 with
                        | (FStar_Pervasives_Native.Some (true ),uu____9933)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____9972)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____10011 -> tm1
                      else
                        (let uu____10027 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____10027
                         then
                           match args with
                           | (t,uu____10029)::[] ->
                               let uu____10046 =
                                 let uu____10047 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____10047.FStar_Syntax_Syntax.n in
                               (match uu____10046 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____10050::[],body,uu____10052) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____10079 -> tm1)
                                | uu____10082 -> tm1)
                           | (uu____10083,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____10084))::
                               (t,uu____10086)::[] ->
                               let uu____10125 =
                                 let uu____10126 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____10126.FStar_Syntax_Syntax.n in
                               (match uu____10125 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____10129::[],body,uu____10131) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____10158 -> tm1)
                                | uu____10161 -> tm1)
                           | uu____10162 -> tm1
                         else
                           (let uu____10172 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____10172
                            then
                              match args with
                              | (t,uu____10174)::[] ->
                                  let uu____10191 =
                                    let uu____10192 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____10192.FStar_Syntax_Syntax.n in
                                  (match uu____10191 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____10195::[],body,uu____10197) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____10224 -> tm1)
                                   | uu____10227 -> tm1)
                              | (uu____10228,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____10229))::
                                  (t,uu____10231)::[] ->
                                  let uu____10270 =
                                    let uu____10271 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____10271.FStar_Syntax_Syntax.n in
                                  (match uu____10270 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____10274::[],body,uu____10276) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____10303 -> tm1)
                                   | uu____10306 -> tm1)
                              | uu____10307 -> tm1
                            else reduce_equality cfg tm1)))))
         | uu____10317 -> tm1)
let is_norm_request:
  'Auu____10324 .
    FStar_Syntax_Syntax.term -> 'Auu____10324 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10337 =
        let uu____10344 =
          let uu____10345 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10345.FStar_Syntax_Syntax.n in
        (uu____10344, args) in
      match uu____10337 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10351::uu____10352::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10356::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10361::uu____10362::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10365 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___174_10377  ->
    match uu___174_10377 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.WHNF  -> [WHNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10383 =
          let uu____10386 =
            let uu____10387 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____10387 in
          [uu____10386] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10383
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____10406 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10406) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10444 =
          FStar_Syntax_Embeddings.unembed_list
            FStar_Syntax_Embeddings.unembed_norm_step s in
        FStar_All.pipe_left tr_norm_steps uu____10444 in
      match args with
      | uu____10457::(tm,uu____10459)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____10482)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____10497)::uu____10498::(tm,uu____10500)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____10540 =
              let uu____10543 = full_norm steps in parse_steps uu____10543 in
            Beta :: uu____10540 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____10552 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___175_10570  ->
    match uu___175_10570 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.pos = uu____10573;
           FStar_Syntax_Syntax.vars = uu____10574;_},uu____10575,uu____10576))::uu____10577
        -> true
    | uu____10584 -> false
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
            (fun uu____10719  ->
               let uu____10720 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____10721 = FStar_Syntax_Print.term_to_string t1 in
               let uu____10722 =
                 let uu____10723 =
                   let uu____10726 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____10726 in
                 stack_to_string uu____10723 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____10720
                 uu____10721 uu____10722);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____10749 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____10774 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____10791 =
                 let uu____10792 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____10793 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____10792 uu____10793 in
               failwith uu____10791
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____10794 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____10811 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____10812 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10813;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____10814;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10817;
                 FStar_Syntax_Syntax.fv_delta = uu____10818;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10819;
                 FStar_Syntax_Syntax.fv_delta = uu____10820;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____10821);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((FStar_Syntax_Util.is_fstar_tactics_embed hd1) ||
                  ((FStar_Syntax_Util.is_fstar_tactics_quote hd1) &&
                     (FStar_List.contains NoDeltaSteps cfg.steps)))
                 || (FStar_Syntax_Util.is_fstar_tactics_by_tactic hd1)
               ->
               let args1 = closures_as_args_delayed cfg env args in
               let hd2 = closure_as_term cfg env hd1 in
               let t2 =
                 let uu___207_10863 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___207_10863.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___207_10863.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____10896 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____10896) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___208_10904 = cfg in
                 let uu____10905 =
                   FStar_List.filter
                     (fun uu___176_10908  ->
                        match uu___176_10908 with
                        | UnfoldOnly uu____10909 -> false
                        | NoDeltaSteps  -> false
                        | uu____10912 -> true) cfg.steps in
                 {
                   steps = uu____10905;
                   tcenv = (uu___208_10904.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___208_10904.primitive_steps)
                 } in
               let uu____10913 = get_norm_request (norm cfg' env []) args in
               (match uu____10913 with
                | (s,tm) ->
                    let delta_level =
                      let uu____10929 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___177_10934  ->
                                match uu___177_10934 with
                                | UnfoldUntil uu____10935 -> true
                                | UnfoldOnly uu____10936 -> true
                                | uu____10939 -> false)) in
                      if uu____10929
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___209_10944 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___209_10944.tcenv);
                        delta_level;
                        primitive_steps = (uu___209_10944.primitive_steps)
                      } in
                    let stack' =
                      let tail1 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let uu____10955 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____10955
                      then
                        let uu____10958 =
                          let uu____10959 =
                            let uu____10964 = FStar_Util.now () in
                            (t1, uu____10964) in
                          Debug uu____10959 in
                        uu____10958 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____10966;
                  FStar_Syntax_Syntax.vars = uu____10967;_},a1::a2::rest)
               ->
               let uu____11015 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11015 with
                | (hd1,uu____11031) ->
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
                    (FStar_Const.Const_reflect uu____11096);
                  FStar_Syntax_Syntax.pos = uu____11097;
                  FStar_Syntax_Syntax.vars = uu____11098;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____11130 = FStar_List.tl stack1 in
               norm cfg env uu____11130 (FStar_Pervasives_Native.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11133;
                  FStar_Syntax_Syntax.vars = uu____11134;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____11166 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11166 with
                | (reify_head,uu____11182) ->
                    let a1 =
                      let uu____11204 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (FStar_Pervasives_Native.fst a) in
                      FStar_Syntax_Subst.compress uu____11204 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____11207);
                            FStar_Syntax_Syntax.pos = uu____11208;
                            FStar_Syntax_Syntax.vars = uu____11209;_},a2::[])
                         ->
                         norm cfg env stack1 (FStar_Pervasives_Native.fst a2)
                     | uu____11243 ->
                         let stack2 =
                           (App
                              (reify_head, FStar_Pervasives_Native.None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11253 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____11253
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11260 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11260
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____11263 =
                      let uu____11270 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11270, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11263 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___178_11284  ->
                         match uu___178_11284 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11287 =
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
                 if uu____11287
                 then false
                 else
                   (let uu____11289 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___179_11296  ->
                              match uu___179_11296 with
                              | UnfoldOnly uu____11297 -> true
                              | uu____11300 -> false)) in
                    match uu____11289 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11304 -> should_delta) in
               (log cfg
                  (fun uu____11312  ->
                     let uu____11313 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11314 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____11315 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11313 uu____11314 uu____11315);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack1 t1
                else
                  (let r_env =
                     let uu____11318 = FStar_Syntax_Syntax.range_of_fv f in
                     FStar_TypeChecker_Env.set_range cfg.tcenv uu____11318 in
                   let uu____11319 =
                     FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                       r_env
                       (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   match uu____11319 with
                   | FStar_Pervasives_Native.None  ->
                       (log cfg
                          (fun uu____11332  ->
                             FStar_Util.print "Tm_fvar case 2\n" []);
                        rebuild cfg env stack1 t1)
                   | FStar_Pervasives_Native.Some (us,t2) ->
                       (log cfg
                          (fun uu____11343  ->
                             let uu____11344 =
                               FStar_Syntax_Print.term_to_string t0 in
                             let uu____11345 =
                               FStar_Syntax_Print.term_to_string t2 in
                             FStar_Util.print2 ">>> Unfolded %s to %s\n"
                               uu____11344 uu____11345);
                        (let t3 =
                           let uu____11347 =
                             FStar_All.pipe_right cfg.steps
                               (FStar_List.contains
                                  (UnfoldUntil
                                     FStar_Syntax_Syntax.Delta_constant)) in
                           if uu____11347
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
                           | (UnivArgs (us',uu____11357))::stack2 ->
                               let env1 =
                                 FStar_All.pipe_right us'
                                   (FStar_List.fold_left
                                      (fun env1  ->
                                         fun u  -> (Univ u) :: env1) env) in
                               norm cfg env1 stack2 t3
                           | uu____11380 when
                               FStar_All.pipe_right cfg.steps
                                 (FStar_List.contains EraseUniverses)
                               -> norm cfg env stack1 t3
                           | uu____11381 ->
                               let uu____11382 =
                                 let uu____11383 =
                                   FStar_Syntax_Print.lid_to_string
                                     (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                 FStar_Util.format1
                                   "Impossible: missing universe instantiation on %s"
                                   uu____11383 in
                               failwith uu____11382
                         else norm cfg env stack1 t3))))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11386 = lookup_bvar env x in
               (match uu____11386 with
                | Univ uu____11387 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11412 = FStar_ST.op_Bang r in
                      (match uu____11412 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11513  ->
                                 let uu____11514 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____11515 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11514
                                   uu____11515);
                            (let uu____11516 =
                               let uu____11517 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____11517.FStar_Syntax_Syntax.n in
                             match uu____11516 with
                             | FStar_Syntax_Syntax.Tm_abs uu____11520 ->
                                 norm cfg env2 stack1 t'
                             | uu____11537 -> rebuild cfg env2 stack1 t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____11589)::uu____11590 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11599)::uu____11600 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11610,uu____11611))::stack_rest ->
                    (match c with
                     | Univ uu____11615 -> norm cfg (c :: env) stack_rest t1
                     | uu____11616 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____11621::[] ->
                              (log cfg
                                 (fun uu____11637  ->
                                    let uu____11638 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11638);
                               norm cfg (c :: env) stack_rest body)
                          | uu____11639::tl1 ->
                              (log cfg
                                 (fun uu____11658  ->
                                    let uu____11659 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11659);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___210_11689 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___210_11689.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____11774  ->
                          let uu____11775 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11775);
                     norm cfg env stack2 t1)
                | (Debug uu____11776)::uu____11777 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11784 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11784
                    else
                      (let uu____11786 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11786 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11810  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11826 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11826
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11836 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11836)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___211_11841 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___211_11841.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___211_11841.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11842 -> lopt in
                           (log cfg
                              (fun uu____11848  ->
                                 let uu____11849 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11849);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___212_11862 = cfg in
                               let uu____11863 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___212_11862.steps);
                                 tcenv = (uu___212_11862.tcenv);
                                 delta_level = (uu___212_11862.delta_level);
                                 primitive_steps = uu____11863
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____11872)::uu____11873 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11880 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11880
                    else
                      (let uu____11882 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11882 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11906  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11922 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11922
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11932 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11932)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___211_11937 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___211_11937.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___211_11937.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11938 -> lopt in
                           (log cfg
                              (fun uu____11944  ->
                                 let uu____11945 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11945);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___212_11958 = cfg in
                               let uu____11959 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___212_11958.steps);
                                 tcenv = (uu___212_11958.tcenv);
                                 delta_level = (uu___212_11958.delta_level);
                                 primitive_steps = uu____11959
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____11968)::uu____11969 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11980 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11980
                    else
                      (let uu____11982 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11982 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12006  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12022 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12022
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12032 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12032)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___211_12037 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___211_12037.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___211_12037.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12038 -> lopt in
                           (log cfg
                              (fun uu____12044  ->
                                 let uu____12045 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12045);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___212_12058 = cfg in
                               let uu____12059 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___212_12058.steps);
                                 tcenv = (uu___212_12058.tcenv);
                                 delta_level = (uu___212_12058.delta_level);
                                 primitive_steps = uu____12059
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____12068)::uu____12069 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12078 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12078
                    else
                      (let uu____12080 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12080 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12104  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12120 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12120
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12130 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12130)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___211_12135 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___211_12135.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___211_12135.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12136 -> lopt in
                           (log cfg
                              (fun uu____12142  ->
                                 let uu____12143 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12143);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___212_12156 = cfg in
                               let uu____12157 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___212_12156.steps);
                                 tcenv = (uu___212_12156.tcenv);
                                 delta_level = (uu___212_12156.delta_level);
                                 primitive_steps = uu____12157
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____12166)::uu____12167 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12182 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12182
                    else
                      (let uu____12184 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12184 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12208  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12224 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12224
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12234 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12234)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___211_12239 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___211_12239.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___211_12239.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12240 -> lopt in
                           (log cfg
                              (fun uu____12246  ->
                                 let uu____12247 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12247);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___212_12260 = cfg in
                               let uu____12261 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___212_12260.steps);
                                 tcenv = (uu___212_12260.tcenv);
                                 delta_level = (uu___212_12260.delta_level);
                                 primitive_steps = uu____12261
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12270 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12270
                    else
                      (let uu____12272 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12272 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12296  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12312 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12312
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12322 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12322)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___211_12327 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___211_12327.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___211_12327.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12328 -> lopt in
                           (log cfg
                              (fun uu____12334  ->
                                 let uu____12335 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12335);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___212_12348 = cfg in
                               let uu____12349 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___212_12348.steps);
                                 tcenv = (uu___212_12348.tcenv);
                                 delta_level = (uu___212_12348.delta_level);
                                 primitive_steps = uu____12349
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
                      (fun uu____12396  ->
                         fun stack2  ->
                           match uu____12396 with
                           | (a,aq) ->
                               let uu____12408 =
                                 let uu____12409 =
                                   let uu____12416 =
                                     let uu____12417 =
                                       let uu____12436 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____12436, false) in
                                     Clos uu____12417 in
                                   (uu____12416, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____12409 in
                               uu____12408 :: stack2) args) in
               (log cfg
                  (fun uu____12488  ->
                     let uu____12489 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12489);
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
                             ((let uu___213_12513 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___213_12513.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___213_12513.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____12514 ->
                      let uu____12519 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12519)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____12522 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____12522 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____12547 =
                          let uu____12548 =
                            let uu____12555 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___214_12557 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___214_12557.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___214_12557.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12555) in
                          FStar_Syntax_Syntax.Tm_refine uu____12548 in
                        mk uu____12547 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____12576 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____12576
               else
                 (let uu____12578 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____12578 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12586 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12598  -> Dummy :: env1) env) in
                        norm_comp cfg uu____12586 c1 in
                      let t2 =
                        let uu____12608 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____12608 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____12667)::uu____12668 -> norm cfg env stack1 t11
                | (Arg uu____12677)::uu____12678 -> norm cfg env stack1 t11
                | (App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____12687;
                       FStar_Syntax_Syntax.vars = uu____12688;_},uu____12689,uu____12690))::uu____12691
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____12698)::uu____12699 ->
                    norm cfg env stack1 t11
                | uu____12708 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____12712  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____12729 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____12729
                        | FStar_Util.Inr c ->
                            let uu____12737 = norm_comp cfg env c in
                            FStar_Util.Inr uu____12737 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____12743 =
                        let uu____12744 =
                          let uu____12745 =
                            let uu____12772 = FStar_Syntax_Util.unascribe t12 in
                            (uu____12772, (tc1, tacopt1), l) in
                          FStar_Syntax_Syntax.Tm_ascribed uu____12745 in
                        mk uu____12744 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____12743)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____12848,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____12849;
                               FStar_Syntax_Syntax.lbunivs = uu____12850;
                               FStar_Syntax_Syntax.lbtyp = uu____12851;
                               FStar_Syntax_Syntax.lbeff = uu____12852;
                               FStar_Syntax_Syntax.lbdef = uu____12853;_}::uu____12854),uu____12855)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____12891 =
                 (let uu____12894 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____12894) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____12896 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____12896))) in
               if uu____12891
               then
                 let env1 =
                   let uu____12900 =
                     let uu____12901 =
                       let uu____12920 =
                         FStar_Util.mk_ref FStar_Pervasives_Native.None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____12920,
                         false) in
                     Clos uu____12901 in
                   uu____12900 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____12972 =
                    let uu____12977 =
                      let uu____12978 =
                        let uu____12979 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____12979
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____12978] in
                    FStar_Syntax_Subst.open_term uu____12977 body in
                  match uu____12972 with
                  | (bs,body1) ->
                      let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                      let lbname =
                        let x =
                          let uu____12993 = FStar_List.hd bs in
                          FStar_Pervasives_Native.fst uu____12993 in
                        FStar_Util.Inl
                          (let uu___215_13003 = x in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___215_13003.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___215_13003.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = ty
                           }) in
                      let lb1 =
                        let uu___216_13005 = lb in
                        let uu____13006 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = lbname;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___216_13005.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = ty;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___216_13005.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____13006
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____13023  -> Dummy :: env1)
                             env) in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let ((true ,lbs),body) when
               (FStar_List.contains CompressUvars cfg.steps) ||
                 ((FStar_List.contains (Exclude Zeta) cfg.steps) &&
                    (FStar_List.contains PureSubtermsWithinComputations
                       cfg.steps))
               ->
               let uu____13046 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____13046 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____13082 =
                               let uu___217_13083 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___217_13083.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___217_13083.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____13082 in
                           let uu____13084 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____13084 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____13104 =
                                   FStar_List.map (fun uu____13108  -> Dummy)
                                     lbs1 in
                                 let uu____13109 =
                                   let uu____13112 =
                                     FStar_List.map
                                       (fun uu____13120  -> Dummy) xs1 in
                                   FStar_List.append uu____13112 env in
                                 FStar_List.append uu____13104 uu____13109 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13132 =
                                       let uu___218_13133 = rc in
                                       let uu____13134 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___218_13133.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13134;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___218_13133.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____13132
                                 | uu____13141 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___219_13145 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___219_13145.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___219_13145.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____13149 =
                        FStar_List.map (fun uu____13153  -> Dummy) lbs2 in
                      FStar_List.append uu____13149 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____13155 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____13155 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___220_13171 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___220_13171.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___220_13171.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____13198 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____13198
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13217 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13268  ->
                        match uu____13268 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____13341 =
                                let uu___221_13342 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___221_13342.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___221_13342.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____13341 in
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
               (match uu____13217 with
                | (rec_env,memos,uu____13470) ->
                    let uu____13499 =
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
                             let uu____13964 =
                               let uu____13965 =
                                 let uu____13984 =
                                   FStar_Util.mk_ref
                                     FStar_Pervasives_Native.None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____13984, false) in
                               Clos uu____13965 in
                             uu____13964 :: env1)
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
                             FStar_Syntax_Syntax.pos = uu____14052;
                             FStar_Syntax_Syntax.vars = uu____14053;_},uu____14054,uu____14055))::uu____14056
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____14063 -> false in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____14073 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____14073
                        then
                          let uu___222_14074 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___222_14074.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps =
                              (uu___222_14074.primitive_steps)
                          }
                        else
                          (let uu___223_14076 = cfg in
                           {
                             steps =
                               (FStar_List.append [Exclude Zeta] cfg.steps);
                             tcenv = (uu___223_14076.tcenv);
                             delta_level = (uu___223_14076.delta_level);
                             primitive_steps =
                               (uu___223_14076.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____14078 =
                         let uu____14079 = FStar_Syntax_Subst.compress head1 in
                         uu____14079.FStar_Syntax_Syntax.n in
                       match uu____14078 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____14097 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____14097 with
                            | (uu____14098,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____14104 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____14112 =
                                         let uu____14113 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____14113.FStar_Syntax_Syntax.n in
                                       match uu____14112 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____14119,uu____14120))
                                           ->
                                           let uu____14129 =
                                             let uu____14130 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____14130.FStar_Syntax_Syntax.n in
                                           (match uu____14129 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____14136,msrc,uu____14138))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____14147 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14147
                                            | uu____14148 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____14149 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____14150 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____14150 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___224_14155 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___224_14155.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___224_14155.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___224_14155.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____14156 =
                                            FStar_List.tl stack1 in
                                          let uu____14157 =
                                            let uu____14158 =
                                              let uu____14161 =
                                                let uu____14162 =
                                                  let uu____14175 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____14175) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____14162 in
                                              FStar_Syntax_Syntax.mk
                                                uu____14161 in
                                            uu____14158
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____14156
                                            uu____14157
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____14191 =
                                            let uu____14192 = is_return body in
                                            match uu____14192 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____14196;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____14197;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____14202 -> false in
                                          if uu____14191
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
                                               let uu____14226 =
                                                 let uu____14229 =
                                                   let uu____14230 =
                                                     let uu____14247 =
                                                       let uu____14250 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____14250] in
                                                     (uu____14247, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc)) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____14230 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____14229 in
                                               uu____14226
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____14266 =
                                                 let uu____14267 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____14267.FStar_Syntax_Syntax.n in
                                               match uu____14266 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____14273::uu____14274::[])
                                                   ->
                                                   let uu____14281 =
                                                     let uu____14284 =
                                                       let uu____14285 =
                                                         let uu____14292 =
                                                           let uu____14295 =
                                                             let uu____14296
                                                               =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____14296 in
                                                           let uu____14297 =
                                                             let uu____14300
                                                               =
                                                               let uu____14301
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____14301 in
                                                             [uu____14300] in
                                                           uu____14295 ::
                                                             uu____14297 in
                                                         (bind1, uu____14292) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____14285 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____14284 in
                                                   uu____14281
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____14309 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____14315 =
                                                 let uu____14318 =
                                                   let uu____14319 =
                                                     let uu____14334 =
                                                       let uu____14337 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____14338 =
                                                         let uu____14341 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____14342 =
                                                           let uu____14345 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____14346 =
                                                             let uu____14349
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____14350
                                                               =
                                                               let uu____14353
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____14354
                                                                 =
                                                                 let uu____14357
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____14357] in
                                                               uu____14353 ::
                                                                 uu____14354 in
                                                             uu____14349 ::
                                                               uu____14350 in
                                                           uu____14345 ::
                                                             uu____14346 in
                                                         uu____14341 ::
                                                           uu____14342 in
                                                       uu____14337 ::
                                                         uu____14338 in
                                                     (bind_inst, uu____14334) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____14319 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____14318 in
                                               uu____14315
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____14365 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____14365 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____14389 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____14389 with
                            | (uu____14390,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____14419 =
                                        let uu____14420 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____14420.FStar_Syntax_Syntax.n in
                                      match uu____14419 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____14426) -> t4
                                      | uu____14431 -> head2 in
                                    let uu____14432 =
                                      let uu____14433 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____14433.FStar_Syntax_Syntax.n in
                                    match uu____14432 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____14439 ->
                                        FStar_Pervasives_Native.None in
                                  let uu____14440 = maybe_extract_fv head2 in
                                  match uu____14440 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____14450 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____14450
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____14455 =
                                          maybe_extract_fv head3 in
                                        match uu____14455 with
                                        | FStar_Pervasives_Native.Some
                                            uu____14460 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____14461 ->
                                            FStar_Pervasives_Native.Some
                                              false in
                                      (head3, action_unfolded)
                                  | uu____14466 ->
                                      (head2, FStar_Pervasives_Native.None) in
                                ((let is_arg_impure uu____14481 =
                                    match uu____14481 with
                                    | (e,q) ->
                                        let uu____14488 =
                                          let uu____14489 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____14489.FStar_Syntax_Syntax.n in
                                        (match uu____14488 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____14504 -> false) in
                                  let uu____14505 =
                                    let uu____14506 =
                                      let uu____14513 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____14513 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____14506 in
                                  if uu____14505
                                  then
                                    let uu____14518 =
                                      let uu____14519 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____14519 in
                                    failwith uu____14518
                                  else ());
                                 (let uu____14521 =
                                    maybe_unfold_action head_app in
                                  match uu____14521 with
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
                                      let uu____14560 = FStar_List.tl stack1 in
                                      norm cfg env uu____14560 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____14574 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____14574 in
                           let uu____14575 = FStar_List.tl stack1 in
                           norm cfg env uu____14575 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____14696  ->
                                     match uu____14696 with
                                     | (pat,wopt,tm) ->
                                         let uu____14744 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____14744))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____14776 = FStar_List.tl stack1 in
                           norm cfg env uu____14776 tm
                       | uu____14777 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.pos = uu____14786;
                             FStar_Syntax_Syntax.vars = uu____14787;_},uu____14788,uu____14789))::uu____14790
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____14797 -> false in
                    if should_reify
                    then
                      let uu____14798 = FStar_List.tl stack1 in
                      let uu____14799 =
                        let uu____14800 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____14800 in
                      norm cfg env uu____14798 uu____14799
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____14803 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____14803
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___225_14812 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___225_14812.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___225_14812.primitive_steps)
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
                | uu____14814 ->
                    if FStar_List.contains Unmeta cfg.steps
                    then norm cfg env stack1 head1
                    else
                      (match stack1 with
                       | uu____14816::uu____14817 ->
                           (match m with
                            | FStar_Syntax_Syntax.Meta_labeled
                                (l,r,uu____14822) ->
                                norm cfg env ((Meta (m, r)) :: stack1) head1
                            | FStar_Syntax_Syntax.Meta_alien (b,s) ->
                                norm cfg env
                                  ((Meta (m, (t1.FStar_Syntax_Syntax.pos)))
                                  :: stack1) head1
                            | FStar_Syntax_Syntax.Meta_pattern args ->
                                let args1 = norm_pattern_args cfg env args in
                                norm cfg env
                                  ((Meta
                                      ((FStar_Syntax_Syntax.Meta_pattern
                                          args1),
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) head1
                            | uu____14847 -> norm cfg env stack1 head1)
                       | [] ->
                           let head2 = norm cfg env [] head1 in
                           let m1 =
                             match m with
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let uu____14861 =
                                   norm_pattern_args cfg env args in
                                 FStar_Syntax_Syntax.Meta_pattern uu____14861
                             | uu____14872 -> m in
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
              let uu____14884 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____14884 with
              | (uu____14885,return_repr) ->
                  let return_inst =
                    let uu____14894 =
                      let uu____14895 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____14895.FStar_Syntax_Syntax.n in
                    match uu____14894 with
                    | FStar_Syntax_Syntax.Tm_uinst
                        (return_tm,uu____14901::[]) ->
                        let uu____14908 =
                          let uu____14911 =
                            let uu____14912 =
                              let uu____14919 =
                                let uu____14922 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____14922] in
                              (return_tm, uu____14919) in
                            FStar_Syntax_Syntax.Tm_uinst uu____14912 in
                          FStar_Syntax_Syntax.mk uu____14911 in
                        uu____14908 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____14930 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____14933 =
                    let uu____14936 =
                      let uu____14937 =
                        let uu____14952 =
                          let uu____14955 = FStar_Syntax_Syntax.as_arg t in
                          let uu____14956 =
                            let uu____14959 = FStar_Syntax_Syntax.as_arg e in
                            [uu____14959] in
                          uu____14955 :: uu____14956 in
                        (return_inst, uu____14952) in
                      FStar_Syntax_Syntax.Tm_app uu____14937 in
                    FStar_Syntax_Syntax.mk uu____14936 in
                  uu____14933 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____14968 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____14968 with
               | FStar_Pervasives_Native.None  ->
                   let uu____14971 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____14971
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____14972;
                     FStar_TypeChecker_Env.mtarget = uu____14973;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____14974;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____14985;
                     FStar_TypeChecker_Env.mtarget = uu____14986;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____14987;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____15005 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____15005)
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
                (fun uu____15061  ->
                   match uu____15061 with
                   | (a,imp) ->
                       let uu____15072 = norm cfg env [] a in
                       (uu____15072, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___226_15089 = comp1 in
            let uu____15092 =
              let uu____15093 =
                let uu____15102 = norm cfg env [] t in
                let uu____15103 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____15102, uu____15103) in
              FStar_Syntax_Syntax.Total uu____15093 in
            {
              FStar_Syntax_Syntax.n = uu____15092;
              FStar_Syntax_Syntax.pos =
                (uu___226_15089.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___226_15089.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___227_15118 = comp1 in
            let uu____15121 =
              let uu____15122 =
                let uu____15131 = norm cfg env [] t in
                let uu____15132 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____15131, uu____15132) in
              FStar_Syntax_Syntax.GTotal uu____15122 in
            {
              FStar_Syntax_Syntax.n = uu____15121;
              FStar_Syntax_Syntax.pos =
                (uu___227_15118.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___227_15118.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____15184  ->
                      match uu____15184 with
                      | (a,i) ->
                          let uu____15195 = norm cfg env [] a in
                          (uu____15195, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___180_15206  ->
                      match uu___180_15206 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____15210 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____15210
                      | f -> f)) in
            let uu___228_15214 = comp1 in
            let uu____15217 =
              let uu____15218 =
                let uu___229_15219 = ct in
                let uu____15220 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____15221 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____15224 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____15220;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___229_15219.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____15221;
                  FStar_Syntax_Syntax.effect_args = uu____15224;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____15218 in
            {
              FStar_Syntax_Syntax.n = uu____15217;
              FStar_Syntax_Syntax.pos =
                (uu___228_15214.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___228_15214.FStar_Syntax_Syntax.vars)
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
            (let uu___230_15242 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___230_15242.tcenv);
               delta_level = (uu___230_15242.delta_level);
               primitive_steps = (uu___230_15242.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____15247 = norm1 t in
          FStar_Syntax_Util.non_informative uu____15247 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____15250 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___231_15269 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.pos =
                (uu___231_15269.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___231_15269.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____15276 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____15276
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
                    let uu___232_15287 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___232_15287.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___232_15287.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___232_15287.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___233_15289 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___233_15289.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___233_15289.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___233_15289.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___233_15289.FStar_Syntax_Syntax.flags)
                    } in
              let uu___234_15290 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos =
                  (uu___234_15290.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___234_15290.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____15292 -> c
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____15295  ->
        match uu____15295 with
        | (x,imp) ->
            let uu____15298 =
              let uu___235_15299 = x in
              let uu____15300 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___235_15299.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___235_15299.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____15300
              } in
            (uu____15298, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____15306 =
          FStar_List.fold_left
            (fun uu____15324  ->
               fun b  ->
                 match uu____15324 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____15306 with | (nbs,uu____15352) -> FStar_List.rev nbs
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
            let uu____15368 =
              let uu___236_15369 = rc in
              let uu____15370 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___236_15369.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____15370;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___236_15369.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____15368
        | uu____15377 -> lopt
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
              ((let uu____15390 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____15390
                then
                  let time_now = FStar_Util.now () in
                  let uu____15392 =
                    let uu____15393 =
                      let uu____15394 =
                        FStar_Util.time_diff time_then time_now in
                      FStar_Pervasives_Native.snd uu____15394 in
                    FStar_Util.string_of_int uu____15393 in
                  let uu____15399 = FStar_Syntax_Print.term_to_string tm in
                  let uu____15400 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                    uu____15392 uu____15399 uu____15400
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___237_15418 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___237_15418.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____15511  ->
                    let uu____15512 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____15512);
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
              let uu____15548 =
                let uu___238_15549 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___238_15549.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___238_15549.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____15548
          | (Arg (Univ uu____15550,uu____15551,uu____15552))::uu____15553 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____15556,uu____15557))::uu____15558 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____15574),aq,r))::stack2 ->
              (log cfg
                 (fun uu____15603  ->
                    let uu____15604 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____15604);
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
                 (let uu____15614 = FStar_ST.op_Bang m in
                  match uu____15614 with
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
                  | FStar_Pervasives_Native.Some (uu____15734,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq)
                          FStar_Pervasives_Native.None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 =
                FStar_Syntax_Syntax.extend_app head1 (t, aq)
                  FStar_Pervasives_Native.None r in
              let uu____15758 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____15758
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____15768  ->
                    let uu____15769 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____15769);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____15774 =
                  log cfg
                    (fun uu____15779  ->
                       let uu____15780 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____15781 =
                         let uu____15782 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____15799  ->
                                   match uu____15799 with
                                   | (p,uu____15809,uu____15810) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____15782
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____15780 uu____15781);
                  (let whnf1 = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___181_15827  ->
                               match uu___181_15827 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____15828 -> false)) in
                     let steps' =
                       let uu____15832 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____15832
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___239_15836 = cfg in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___239_15836.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___239_15836.primitive_steps)
                     } in
                   let norm_or_whnf env2 t1 =
                     if whnf1
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____15880 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____15903 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____15969  ->
                                   fun uu____15970  ->
                                     match (uu____15969, uu____15970) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____16073 = norm_pat env3 p1 in
                                         (match uu____16073 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____15903 with
                          | (pats1,env3) ->
                              ((let uu___240_16175 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.p =
                                    (uu___240_16175.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___241_16194 = x in
                           let uu____16195 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___241_16194.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___241_16194.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16195
                           } in
                         ((let uu___242_16203 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.p =
                               (uu___242_16203.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___243_16208 = x in
                           let uu____16209 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___243_16208.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___243_16208.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16209
                           } in
                         ((let uu___244_16217 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.p =
                               (uu___244_16217.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___245_16227 = x in
                           let uu____16228 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___245_16227.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___245_16227.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16228
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___246_16237 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.p =
                               (uu___246_16237.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf1 -> branches
                     | uu____16241 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____16255 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____16255 with
                                 | (p,wopt,e) ->
                                     let uu____16275 = norm_pat env1 p in
                                     (match uu____16275 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Pervasives_Native.Some w
                                                ->
                                                let uu____16306 =
                                                  norm_or_whnf env2 w in
                                                FStar_Pervasives_Native.Some
                                                  uu____16306 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____16312 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____16312) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____16322) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____16327 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____16328;
                        FStar_Syntax_Syntax.fv_delta = uu____16329;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Data_ctor );_}
                      -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____16330;
                        FStar_Syntax_Syntax.fv_delta = uu____16331;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Record_ctor uu____16332);_}
                      -> true
                  | uu____16339 -> false in
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
                  let uu____16468 =
                    FStar_Syntax_Util.head_and_args scrutinee1 in
                  match uu____16468 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var uu____16517 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_wild uu____16520 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____16523 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee1.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____16542 ->
                                let uu____16543 =
                                  let uu____16544 = is_cons head1 in
                                  Prims.op_Negation uu____16544 in
                                FStar_Util.Inr uu____16543)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____16565 =
                             let uu____16566 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____16566.FStar_Syntax_Syntax.n in
                           (match uu____16565 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____16576 ->
                                let uu____16577 =
                                  let uu____16578 = is_cons head1 in
                                  Prims.op_Negation uu____16578 in
                                FStar_Util.Inr uu____16577))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____16631)::rest_a,(p1,uu____16634)::rest_p) ->
                      let uu____16678 = matches_pat t1 p1 in
                      (match uu____16678 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____16703 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____16805 = matches_pat scrutinee1 p1 in
                      (match uu____16805 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____16825  ->
                                 let uu____16826 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____16827 =
                                   let uu____16828 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____16828
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____16826 uu____16827);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____16845 =
                                        let uu____16846 =
                                          let uu____16865 =
                                            FStar_Util.mk_ref
                                              (FStar_Pervasives_Native.Some
                                                 ([], t1)) in
                                          ([], t1, uu____16865, false) in
                                        Clos uu____16846 in
                                      uu____16845 :: env2) env1 s in
                             let uu____16918 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____16918))) in
                let uu____16919 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____16919
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___182_16942  ->
                match uu___182_16942 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____16946 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____16952 -> d in
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
            let uu___247_16981 = config s e in
            {
              steps = (uu___247_16981.steps);
              tcenv = (uu___247_16981.tcenv);
              delta_level = (uu___247_16981.delta_level);
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
      fun t  -> let uu____17006 = config s e in norm_comp uu____17006 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____17015 = config [] env in norm_universe uu____17015 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let uu____17024 = config [] env in ghost_to_pure_aux uu____17024 [] c
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
        let uu____17038 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____17038 in
      let uu____17039 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____17039
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___248_17041 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___248_17041.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___248_17041.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____17044  ->
                    let uu____17045 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____17045))
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
            ((let uu____17064 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____17064);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____17077 = config [AllowUnboundUniverses] env in
          norm_comp uu____17077 [] c
        with
        | e ->
            ((let uu____17084 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____17084);
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
                   let uu____17124 =
                     let uu____17125 =
                       let uu____17132 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____17132) in
                     FStar_Syntax_Syntax.Tm_refine uu____17125 in
                   mk uu____17124 t01.FStar_Syntax_Syntax.pos
               | uu____17137 -> t2)
          | uu____17138 -> t2 in
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
        let uu____17190 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____17190 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____17219 ->
                 let uu____17226 = FStar_Syntax_Util.abs_formals e in
                 (match uu____17226 with
                  | (actuals,uu____17236,uu____17237) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____17251 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____17251 with
                         | (binders,args) ->
                             let uu____17268 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____17268
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
      | uu____17278 ->
          let uu____17279 = FStar_Syntax_Util.head_and_args t in
          (match uu____17279 with
           | (head1,args) ->
               let uu____17316 =
                 let uu____17317 = FStar_Syntax_Subst.compress head1 in
                 uu____17317.FStar_Syntax_Syntax.n in
               (match uu____17316 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____17320,thead) ->
                    let uu____17346 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____17346 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____17388 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___253_17396 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___253_17396.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___253_17396.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___253_17396.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___253_17396.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___253_17396.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___253_17396.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___253_17396.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___253_17396.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___253_17396.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___253_17396.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___253_17396.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___253_17396.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___253_17396.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___253_17396.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___253_17396.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___253_17396.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___253_17396.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___253_17396.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___253_17396.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___253_17396.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___253_17396.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___253_17396.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___253_17396.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___253_17396.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___253_17396.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___253_17396.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___253_17396.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___253_17396.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___253_17396.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___253_17396.FStar_TypeChecker_Env.dsenv)
                                 }) t in
                            match uu____17388 with
                            | (uu____17397,ty,uu____17399) ->
                                eta_expand_with_type env t ty))
                | uu____17400 ->
                    let uu____17401 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___254_17409 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___254_17409.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___254_17409.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___254_17409.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___254_17409.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___254_17409.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___254_17409.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___254_17409.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___254_17409.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___254_17409.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___254_17409.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___254_17409.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___254_17409.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___254_17409.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___254_17409.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___254_17409.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___254_17409.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___254_17409.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___254_17409.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___254_17409.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___254_17409.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___254_17409.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___254_17409.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___254_17409.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___254_17409.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___254_17409.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___254_17409.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___254_17409.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___254_17409.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___254_17409.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___254_17409.FStar_TypeChecker_Env.dsenv)
                         }) t in
                    (match uu____17401 with
                     | (uu____17410,ty,uu____17412) ->
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
            | (uu____17490,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____17496,FStar_Util.Inl t) ->
                let uu____17502 =
                  let uu____17505 =
                    let uu____17506 =
                      let uu____17519 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____17519) in
                    FStar_Syntax_Syntax.Tm_arrow uu____17506 in
                  FStar_Syntax_Syntax.mk uu____17505 in
                uu____17502 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____17523 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____17523 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____17550 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____17605 ->
                    let uu____17606 =
                      let uu____17615 =
                        let uu____17616 = FStar_Syntax_Subst.compress t3 in
                        uu____17616.FStar_Syntax_Syntax.n in
                      (uu____17615, tc) in
                    (match uu____17606 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____17641) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____17678) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____17717,FStar_Util.Inl uu____17718) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____17741 -> failwith "Impossible") in
              (match uu____17550 with
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
          let uu____17850 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____17850 with
          | (univ_names1,binders1,tc) ->
              let uu____17908 = FStar_Util.left tc in
              (univ_names1, binders1, uu____17908)
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
          let uu____17947 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____17947 with
          | (univ_names1,binders1,tc) ->
              let uu____18007 = FStar_Util.right tc in
              (univ_names1, binders1, uu____18007)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____18042 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____18042 with
           | (univ_names1,binders1,typ1) ->
               let uu___255_18070 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___255_18070.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___255_18070.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___255_18070.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___255_18070.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___256_18091 = s in
          let uu____18092 =
            let uu____18093 =
              let uu____18102 = FStar_List.map (elim_uvars env) sigs in
              (uu____18102, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____18093 in
          {
            FStar_Syntax_Syntax.sigel = uu____18092;
            FStar_Syntax_Syntax.sigrng =
              (uu___256_18091.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___256_18091.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___256_18091.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___256_18091.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____18119 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____18119 with
           | (univ_names1,uu____18137,typ1) ->
               let uu___257_18151 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___257_18151.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___257_18151.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___257_18151.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___257_18151.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____18157 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____18157 with
           | (univ_names1,uu____18175,typ1) ->
               let uu___258_18189 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___258_18189.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___258_18189.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___258_18189.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___258_18189.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____18223 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____18223 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____18246 =
                            let uu____18247 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____18247 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____18246 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___259_18250 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___259_18250.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___259_18250.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___260_18251 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___260_18251.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___260_18251.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___260_18251.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___260_18251.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___261_18263 = s in
          let uu____18264 =
            let uu____18265 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____18265 in
          {
            FStar_Syntax_Syntax.sigel = uu____18264;
            FStar_Syntax_Syntax.sigrng =
              (uu___261_18263.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___261_18263.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___261_18263.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___261_18263.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____18269 = elim_uvars_aux_t env us [] t in
          (match uu____18269 with
           | (us1,uu____18287,t1) ->
               let uu___262_18301 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___262_18301.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___262_18301.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___262_18301.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___262_18301.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____18302 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____18304 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____18304 with
           | (univs1,binders,signature) ->
               let uu____18332 =
                 let uu____18341 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____18341 with
                 | (univs_opening,univs2) ->
                     let uu____18368 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____18368) in
               (match uu____18332 with
                | (univs_opening,univs_closing) ->
                    let uu____18385 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____18391 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____18392 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____18391, uu____18392) in
                    (match uu____18385 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____18414 =
                           match uu____18414 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____18432 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____18432 with
                                | (us1,t1) ->
                                    let uu____18443 =
                                      let uu____18448 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____18455 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____18448, uu____18455) in
                                    (match uu____18443 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____18468 =
                                           let uu____18473 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____18482 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____18473, uu____18482) in
                                         (match uu____18468 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____18498 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____18498 in
                                              let uu____18499 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____18499 with
                                               | (uu____18520,uu____18521,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____18536 =
                                                       let uu____18537 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____18537 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____18536 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____18542 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____18542 with
                           | (uu____18555,uu____18556,t1) -> t1 in
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
                             | uu____18616 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____18633 =
                               let uu____18634 =
                                 FStar_Syntax_Subst.compress body in
                               uu____18634.FStar_Syntax_Syntax.n in
                             match uu____18633 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____18693 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____18722 =
                               let uu____18723 =
                                 FStar_Syntax_Subst.compress t in
                               uu____18723.FStar_Syntax_Syntax.n in
                             match uu____18722 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____18744) ->
                                 let uu____18765 = destruct_action_body body in
                                 (match uu____18765 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____18810 ->
                                 let uu____18811 = destruct_action_body t in
                                 (match uu____18811 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____18860 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____18860 with
                           | (action_univs,t) ->
                               let uu____18869 = destruct_action_typ_templ t in
                               (match uu____18869 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___263_18910 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___263_18910.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___263_18910.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___264_18912 = ed in
                           let uu____18913 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____18914 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____18915 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____18916 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____18917 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____18918 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____18919 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____18920 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____18921 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____18922 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____18923 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____18924 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____18925 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____18926 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___264_18912.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___264_18912.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____18913;
                             FStar_Syntax_Syntax.bind_wp = uu____18914;
                             FStar_Syntax_Syntax.if_then_else = uu____18915;
                             FStar_Syntax_Syntax.ite_wp = uu____18916;
                             FStar_Syntax_Syntax.stronger = uu____18917;
                             FStar_Syntax_Syntax.close_wp = uu____18918;
                             FStar_Syntax_Syntax.assert_p = uu____18919;
                             FStar_Syntax_Syntax.assume_p = uu____18920;
                             FStar_Syntax_Syntax.null_wp = uu____18921;
                             FStar_Syntax_Syntax.trivial = uu____18922;
                             FStar_Syntax_Syntax.repr = uu____18923;
                             FStar_Syntax_Syntax.return_repr = uu____18924;
                             FStar_Syntax_Syntax.bind_repr = uu____18925;
                             FStar_Syntax_Syntax.actions = uu____18926
                           } in
                         let uu___265_18929 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___265_18929.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___265_18929.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___265_18929.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___265_18929.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___183_18946 =
            match uu___183_18946 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____18973 = elim_uvars_aux_t env us [] t in
                (match uu____18973 with
                 | (us1,uu____18997,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___266_19016 = sub_eff in
            let uu____19017 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____19020 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___266_19016.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___266_19016.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____19017;
              FStar_Syntax_Syntax.lift = uu____19020
            } in
          let uu___267_19023 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___267_19023.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___267_19023.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___267_19023.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___267_19023.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____19033 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____19033 with
           | (univ_names1,binders1,comp1) ->
               let uu___268_19067 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___268_19067.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___268_19067.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___268_19067.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___268_19067.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____19078 -> s