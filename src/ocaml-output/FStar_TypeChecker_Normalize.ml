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
         | uu____4466 -> FStar_Pervasives_Native.None) in
  let arg_as_string uu____4476 =
    match uu____4476 with
    | (a,uu____4484) ->
        let uu____4487 =
          let uu____4488 = FStar_Syntax_Subst.compress a in
          uu____4488.FStar_Syntax_Syntax.n in
        (match uu____4487 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____4494)) -> FStar_Pervasives_Native.Some s
         | uu____4495 -> FStar_Pervasives_Native.None) in
  let arg_as_list f uu____4521 =
    match uu____4521 with
    | (a,uu____4535) ->
        let rec sequence l =
          match l with
          | [] -> FStar_Pervasives_Native.Some []
          | (FStar_Pervasives_Native.None )::uu____4564 ->
              FStar_Pervasives_Native.None
          | (FStar_Pervasives_Native.Some x)::xs ->
              let uu____4581 = sequence xs in
              (match uu____4581 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some xs' ->
                   FStar_Pervasives_Native.Some (x :: xs')) in
        let uu____4601 = FStar_Syntax_Util.list_elements a in
        (match uu____4601 with
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some elts ->
             let uu____4619 =
               FStar_List.map
                 (fun x  ->
                    let uu____4629 = FStar_Syntax_Syntax.as_arg x in
                    f uu____4629) elts in
             sequence uu____4619) in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4667 = f a in FStar_Pervasives_Native.Some uu____4667
    | uu____4668 -> FStar_Pervasives_Native.None in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4718 = f a0 a1 in FStar_Pervasives_Native.Some uu____4718
    | uu____4719 -> FStar_Pervasives_Native.None in
  let unary_op as_a f r args =
    let uu____4768 = FStar_List.map as_a args in lift_unary (f r) uu____4768 in
  let binary_op as_a f r args =
    let uu____4824 = FStar_List.map as_a args in lift_binary (f r) uu____4824 in
  let as_primitive_step uu____4848 =
    match uu____4848 with
    | (l,arity,f) ->
        { name = l; arity; strong_reduction_ok = true; interpretation = f } in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  -> fun x  -> let uu____4896 = f x in int_as_const r uu____4896) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  -> let uu____4924 = f x y in int_as_const r uu____4924) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  -> fun x  -> let uu____4945 = f x in bool_as_const r uu____4945) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  -> let uu____4973 = f x y in bool_as_const r uu____4973) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  -> let uu____5001 = f x y in string_as_const r uu____5001) in
  let list_of_string' rng s =
    let name l =
      let uu____5015 =
        let uu____5016 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____5016 in
      mk uu____5015 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____5044 =
      let uu____5047 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____5047 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____5044 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in int_as_const rng r in
  let string_concat' rng args =
    match args with
    | a1::a2::[] ->
        let uu____5122 = arg_as_string a1 in
        (match uu____5122 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5128 = arg_as_list arg_as_string a2 in
             (match uu____5128 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____5141 = string_as_const rng r in
                  FStar_Pervasives_Native.Some uu____5141
              | uu____5142 -> FStar_Pervasives_Native.None)
         | uu____5147 -> FStar_Pervasives_Native.None)
    | uu____5150 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____5164 = FStar_Util.string_of_int i in
    string_as_const rng uu____5164 in
  let string_of_bool1 rng b =
    string_as_const rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____5180 = FStar_Util.string_of_int i in
    string_as_const rng uu____5180 in
  let string_of_bool2 rng b =
    string_as_const rng (if b then "true" else "false") in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r in
  let range_of1 uu____5210 args =
    match args with
    | uu____5222::(t,uu____5224)::[] ->
        let uu____5253 = term_of_range t.FStar_Syntax_Syntax.pos in
        FStar_Pervasives_Native.Some uu____5253
    | uu____5258 -> FStar_Pervasives_Native.None in
  let set_range_of1 r args =
    match args with
    | uu____5290::(t,uu____5292)::(r1,uu____5294)::[] ->
        let r2 = FStar_Syntax_Embeddings.unembed_range r1 in
        FStar_Pervasives_Native.Some
          (let uu___202_5319 = t in
           {
             FStar_Syntax_Syntax.n = (uu___202_5319.FStar_Syntax_Syntax.n);
             FStar_Syntax_Syntax.pos = r2;
             FStar_Syntax_Syntax.vars =
               (uu___202_5319.FStar_Syntax_Syntax.vars)
           })
    | uu____5320 -> FStar_Pervasives_Native.None in
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
                                                      let uu____6097 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "set_range_of"] in
                                                      (uu____6097,
                                                        (Prims.parse_int "3"),
                                                        set_range_of1) in
                                                    let uu____6110 =
                                                      let uu____6131 =
                                                        let uu____6150 =
                                                          FStar_Parser_Const.p2l
                                                            ["Prims";
                                                            "mk_range"] in
                                                        (uu____6150,
                                                          (Prims.parse_int
                                                             "5"), mk_range1) in
                                                      [uu____6131] in
                                                    uu____6078 :: uu____6110 in
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
      let uu____6755 =
        let uu____6756 =
          let uu____6757 = FStar_Syntax_Syntax.as_arg c in [uu____6757] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6756 in
      uu____6755 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____6792 =
              let uu____6805 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____6805, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____6824  ->
                        fun uu____6825  ->
                          match (uu____6824, uu____6825) with
                          | ((int_to_t1,x),(uu____6844,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____6854 =
              let uu____6869 =
                let uu____6882 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____6882, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____6901  ->
                          fun uu____6902  ->
                            match (uu____6901, uu____6902) with
                            | ((int_to_t1,x),(uu____6921,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____6931 =
                let uu____6946 =
                  let uu____6959 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____6959, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____6978  ->
                            fun uu____6979  ->
                              match (uu____6978, uu____6979) with
                              | ((int_to_t1,x),(uu____6998,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____6946] in
              uu____6869 :: uu____6931 in
            uu____6792 :: uu____6854)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop r args =
    match args with
    | (_typ,uu____7094)::(a1,uu____7096)::(a2,uu____7098)::[] ->
        let uu____7135 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____7135 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___203_7141 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___203_7141.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___203_7141.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___204_7145 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___204_7145.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___204_7145.FStar_Syntax_Syntax.vars)
                })
         | uu____7146 -> FStar_Pervasives_Native.None)
    | (_typ,uu____7148)::uu____7149::(a1,uu____7151)::(a2,uu____7153)::[] ->
        let uu____7202 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____7202 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___203_7208 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___203_7208.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___203_7208.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___204_7212 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___204_7212.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___204_7212.FStar_Syntax_Syntax.vars)
                })
         | uu____7213 -> FStar_Pervasives_Native.None)
    | uu____7214 -> failwith "Unexpected number of arguments" in
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
      let uu____7227 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops cfg.steps) in
      if uu____7227
      then tm
      else
        (let uu____7229 = FStar_Syntax_Util.head_and_args tm in
         match uu____7229 with
         | (head1,args) ->
             let uu____7266 =
               let uu____7267 = FStar_Syntax_Util.un_uinst head1 in
               uu____7267.FStar_Syntax_Syntax.n in
             (match uu____7266 with
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____7271 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps in
                  (match uu____7271 with
                   | FStar_Pervasives_Native.None  -> tm
                   | FStar_Pervasives_Native.Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then tm
                       else
                         (let uu____7284 =
                            prim_step.interpretation
                              head1.FStar_Syntax_Syntax.pos args in
                          match uu____7284 with
                          | FStar_Pervasives_Native.None  -> tm
                          | FStar_Pervasives_Native.Some reduced -> reduced))
              | uu____7288 -> tm))
let reduce_equality:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___205_7299 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___205_7299.tcenv);
           delta_level = (uu___205_7299.delta_level);
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
        let uu___206_7323 = t in
        {
          FStar_Syntax_Syntax.n = (uu___206_7323.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___206_7323.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid ->
            FStar_Pervasives_Native.Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid ->
            FStar_Pervasives_Native.Some false
        | uu____7340 -> FStar_Pervasives_Native.None in
      let simplify1 arg = ((simp_t (FStar_Pervasives_Native.fst arg)), arg) in
      let tm1 = reduce_primops cfg tm in
      let uu____7380 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps) in
      if uu____7380
      then tm1
      else
        (match tm1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.pos = uu____7383;
                     FStar_Syntax_Syntax.vars = uu____7384;_},uu____7385);
                FStar_Syntax_Syntax.pos = uu____7386;
                FStar_Syntax_Syntax.vars = uu____7387;_},args)
             ->
             let uu____7413 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
             if uu____7413
             then
               let uu____7414 =
                 FStar_All.pipe_right args (FStar_List.map simplify1) in
               (match uu____7414 with
                | (FStar_Pervasives_Native.Some (true ),uu____7469)::
                    (uu____7470,(arg,uu____7472))::[] -> arg
                | (uu____7537,(arg,uu____7539))::(FStar_Pervasives_Native.Some
                                                  (true ),uu____7540)::[]
                    -> arg
                | (FStar_Pervasives_Native.Some (false ),uu____7605)::uu____7606::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____7669::(FStar_Pervasives_Native.Some (false
                               ),uu____7670)::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____7733 -> tm1)
             else
               (let uu____7749 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
                if uu____7749
                then
                  let uu____7750 =
                    FStar_All.pipe_right args (FStar_List.map simplify1) in
                  match uu____7750 with
                  | (FStar_Pervasives_Native.Some (true ),uu____7805)::uu____7806::[]
                      -> w FStar_Syntax_Util.t_true
                  | uu____7869::(FStar_Pervasives_Native.Some (true
                                 ),uu____7870)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____7933)::
                      (uu____7934,(arg,uu____7936))::[] -> arg
                  | (uu____8001,(arg,uu____8003))::(FStar_Pervasives_Native.Some
                                                    (false ),uu____8004)::[]
                      -> arg
                  | uu____8069 -> tm1
                else
                  (let uu____8085 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.imp_lid in
                   if uu____8085
                   then
                     let uu____8086 =
                       FStar_All.pipe_right args (FStar_List.map simplify1) in
                     match uu____8086 with
                     | uu____8141::(FStar_Pervasives_Native.Some (true
                                    ),uu____8142)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____8205)::uu____8206::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____8269)::
                         (uu____8270,(arg,uu____8272))::[] -> arg
                     | (uu____8337,(p,uu____8339))::(uu____8340,(q,uu____8342))::[]
                         ->
                         let uu____8407 = FStar_Syntax_Util.term_eq p q in
                         (if uu____8407
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____8409 -> tm1
                   else
                     (let uu____8425 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____8425
                      then
                        let uu____8426 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1) in
                        match uu____8426 with
                        | (FStar_Pervasives_Native.Some (true ),uu____8481)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____8520)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____8559 -> tm1
                      else
                        (let uu____8575 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____8575
                         then
                           match args with
                           | (t,uu____8577)::[] ->
                               let uu____8594 =
                                 let uu____8595 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____8595.FStar_Syntax_Syntax.n in
                               (match uu____8594 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____8598::[],body,uu____8600) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____8627 -> tm1)
                                | uu____8630 -> tm1)
                           | (uu____8631,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____8632))::
                               (t,uu____8634)::[] ->
                               let uu____8673 =
                                 let uu____8674 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____8674.FStar_Syntax_Syntax.n in
                               (match uu____8673 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____8677::[],body,uu____8679) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____8706 -> tm1)
                                | uu____8709 -> tm1)
                           | uu____8710 -> tm1
                         else
                           (let uu____8720 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____8720
                            then
                              match args with
                              | (t,uu____8722)::[] ->
                                  let uu____8739 =
                                    let uu____8740 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____8740.FStar_Syntax_Syntax.n in
                                  (match uu____8739 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____8743::[],body,uu____8745) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____8772 -> tm1)
                                   | uu____8775 -> tm1)
                              | (uu____8776,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____8777))::
                                  (t,uu____8779)::[] ->
                                  let uu____8818 =
                                    let uu____8819 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____8819.FStar_Syntax_Syntax.n in
                                  (match uu____8818 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____8822::[],body,uu____8824) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____8851 -> tm1)
                                   | uu____8854 -> tm1)
                              | uu____8855 -> tm1
                            else
                              (let uu____8865 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.b2t_lid in
                               if uu____8865
                               then
                                 match args with
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (true ));
                                      FStar_Syntax_Syntax.pos = uu____8866;
                                      FStar_Syntax_Syntax.vars = uu____8867;_},uu____8868)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (false ));
                                      FStar_Syntax_Syntax.pos = uu____8885;
                                      FStar_Syntax_Syntax.vars = uu____8886;_},uu____8887)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | uu____8904 -> tm1
                               else reduce_equality cfg tm1))))))
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                FStar_Syntax_Syntax.pos = uu____8915;
                FStar_Syntax_Syntax.vars = uu____8916;_},args)
             ->
             let uu____8938 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
             if uu____8938
             then
               let uu____8939 =
                 FStar_All.pipe_right args (FStar_List.map simplify1) in
               (match uu____8939 with
                | (FStar_Pervasives_Native.Some (true ),uu____8994)::
                    (uu____8995,(arg,uu____8997))::[] -> arg
                | (uu____9062,(arg,uu____9064))::(FStar_Pervasives_Native.Some
                                                  (true ),uu____9065)::[]
                    -> arg
                | (FStar_Pervasives_Native.Some (false ),uu____9130)::uu____9131::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____9194::(FStar_Pervasives_Native.Some (false
                               ),uu____9195)::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____9258 -> tm1)
             else
               (let uu____9274 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
                if uu____9274
                then
                  let uu____9275 =
                    FStar_All.pipe_right args (FStar_List.map simplify1) in
                  match uu____9275 with
                  | (FStar_Pervasives_Native.Some (true ),uu____9330)::uu____9331::[]
                      -> w FStar_Syntax_Util.t_true
                  | uu____9394::(FStar_Pervasives_Native.Some (true
                                 ),uu____9395)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____9458)::
                      (uu____9459,(arg,uu____9461))::[] -> arg
                  | (uu____9526,(arg,uu____9528))::(FStar_Pervasives_Native.Some
                                                    (false ),uu____9529)::[]
                      -> arg
                  | uu____9594 -> tm1
                else
                  (let uu____9610 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.imp_lid in
                   if uu____9610
                   then
                     let uu____9611 =
                       FStar_All.pipe_right args (FStar_List.map simplify1) in
                     match uu____9611 with
                     | uu____9666::(FStar_Pervasives_Native.Some (true
                                    ),uu____9667)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____9730)::uu____9731::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____9794)::
                         (uu____9795,(arg,uu____9797))::[] -> arg
                     | (uu____9862,(p,uu____9864))::(uu____9865,(q,uu____9867))::[]
                         ->
                         let uu____9932 = FStar_Syntax_Util.term_eq p q in
                         (if uu____9932
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____9934 -> tm1
                   else
                     (let uu____9950 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____9950
                      then
                        let uu____9951 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1) in
                        match uu____9951 with
                        | (FStar_Pervasives_Native.Some (true ),uu____10006)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____10045)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____10084 -> tm1
                      else
                        (let uu____10100 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____10100
                         then
                           match args with
                           | (t,uu____10102)::[] ->
                               let uu____10119 =
                                 let uu____10120 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____10120.FStar_Syntax_Syntax.n in
                               (match uu____10119 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____10123::[],body,uu____10125) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____10152 -> tm1)
                                | uu____10155 -> tm1)
                           | (uu____10156,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____10157))::
                               (t,uu____10159)::[] ->
                               let uu____10198 =
                                 let uu____10199 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____10199.FStar_Syntax_Syntax.n in
                               (match uu____10198 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____10202::[],body,uu____10204) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____10231 -> tm1)
                                | uu____10234 -> tm1)
                           | uu____10235 -> tm1
                         else
                           (let uu____10245 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____10245
                            then
                              match args with
                              | (t,uu____10247)::[] ->
                                  let uu____10264 =
                                    let uu____10265 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____10265.FStar_Syntax_Syntax.n in
                                  (match uu____10264 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____10268::[],body,uu____10270) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____10297 -> tm1)
                                   | uu____10300 -> tm1)
                              | (uu____10301,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____10302))::
                                  (t,uu____10304)::[] ->
                                  let uu____10343 =
                                    let uu____10344 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____10344.FStar_Syntax_Syntax.n in
                                  (match uu____10343 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____10347::[],body,uu____10349) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____10376 -> tm1)
                                   | uu____10379 -> tm1)
                              | uu____10380 -> tm1
                            else
                              (let uu____10390 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.b2t_lid in
                               if uu____10390
                               then
                                 match args with
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (true ));
                                      FStar_Syntax_Syntax.pos = uu____10391;
                                      FStar_Syntax_Syntax.vars = uu____10392;_},uu____10393)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (false ));
                                      FStar_Syntax_Syntax.pos = uu____10410;
                                      FStar_Syntax_Syntax.vars = uu____10411;_},uu____10412)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | uu____10429 -> tm1
                               else reduce_equality cfg tm1))))))
         | uu____10439 -> tm1)
let is_norm_request:
  'Auu____10446 .
    FStar_Syntax_Syntax.term -> 'Auu____10446 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10459 =
        let uu____10466 =
          let uu____10467 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10467.FStar_Syntax_Syntax.n in
        (uu____10466, args) in
      match uu____10459 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10473::uu____10474::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10478::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10483::uu____10484::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10487 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___174_10499  ->
    match uu___174_10499 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.WHNF  -> [WHNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10505 =
          let uu____10508 =
            let uu____10509 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____10509 in
          [uu____10508] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10505
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____10528 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10528) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10566 =
          FStar_Syntax_Embeddings.unembed_list
            FStar_Syntax_Embeddings.unembed_norm_step s in
        FStar_All.pipe_left tr_norm_steps uu____10566 in
      match args with
      | uu____10579::(tm,uu____10581)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____10604)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____10619)::uu____10620::(tm,uu____10622)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____10662 =
              let uu____10665 = full_norm steps in parse_steps uu____10665 in
            Beta :: uu____10662 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____10674 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___175_10692  ->
    match uu___175_10692 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.pos = uu____10695;
           FStar_Syntax_Syntax.vars = uu____10696;_},uu____10697,uu____10698))::uu____10699
        -> true
    | uu____10706 -> false
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
            (fun uu____10841  ->
               let uu____10842 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____10843 = FStar_Syntax_Print.term_to_string t1 in
               let uu____10844 =
                 let uu____10845 =
                   let uu____10848 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____10848 in
                 stack_to_string uu____10845 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____10842
                 uu____10843 uu____10844);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____10871 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____10896 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____10913 =
                 let uu____10914 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____10915 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____10914 uu____10915 in
               failwith uu____10913
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____10916 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____10933 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____10934 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10935;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____10936;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10939;
                 FStar_Syntax_Syntax.fv_delta = uu____10940;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10941;
                 FStar_Syntax_Syntax.fv_delta = uu____10942;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____10943);_}
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
                 let uu___207_10985 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___207_10985.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___207_10985.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____11018 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____11018) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___208_11026 = cfg in
                 let uu____11027 =
                   FStar_List.filter
                     (fun uu___176_11030  ->
                        match uu___176_11030 with
                        | UnfoldOnly uu____11031 -> false
                        | NoDeltaSteps  -> false
                        | uu____11034 -> true) cfg.steps in
                 {
                   steps = uu____11027;
                   tcenv = (uu___208_11026.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___208_11026.primitive_steps)
                 } in
               let uu____11035 = get_norm_request (norm cfg' env []) args in
               (match uu____11035 with
                | (s,tm) ->
                    let delta_level =
                      let uu____11051 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___177_11056  ->
                                match uu___177_11056 with
                                | UnfoldUntil uu____11057 -> true
                                | UnfoldOnly uu____11058 -> true
                                | uu____11061 -> false)) in
                      if uu____11051
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___209_11066 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___209_11066.tcenv);
                        delta_level;
                        primitive_steps = (uu___209_11066.primitive_steps)
                      } in
                    let stack' =
                      let tail1 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let uu____11077 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____11077
                      then
                        let uu____11080 =
                          let uu____11081 =
                            let uu____11086 = FStar_Util.now () in
                            (t1, uu____11086) in
                          Debug uu____11081 in
                        uu____11080 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11088;
                  FStar_Syntax_Syntax.vars = uu____11089;_},a1::a2::rest)
               ->
               let uu____11137 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11137 with
                | (hd1,uu____11153) ->
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
                    (FStar_Const.Const_reflect uu____11218);
                  FStar_Syntax_Syntax.pos = uu____11219;
                  FStar_Syntax_Syntax.vars = uu____11220;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____11252 = FStar_List.tl stack1 in
               norm cfg env uu____11252 (FStar_Pervasives_Native.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11255;
                  FStar_Syntax_Syntax.vars = uu____11256;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____11288 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11288 with
                | (reify_head,uu____11304) ->
                    let a1 =
                      let uu____11326 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (FStar_Pervasives_Native.fst a) in
                      FStar_Syntax_Subst.compress uu____11326 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____11329);
                            FStar_Syntax_Syntax.pos = uu____11330;
                            FStar_Syntax_Syntax.vars = uu____11331;_},a2::[])
                         ->
                         norm cfg env stack1 (FStar_Pervasives_Native.fst a2)
                     | uu____11365 ->
                         let stack2 =
                           (App
                              (reify_head, FStar_Pervasives_Native.None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11375 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____11375
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11382 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11382
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____11385 =
                      let uu____11392 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11392, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11385 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___178_11406  ->
                         match uu___178_11406 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11409 =
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
                 if uu____11409
                 then false
                 else
                   (let uu____11411 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___179_11418  ->
                              match uu___179_11418 with
                              | UnfoldOnly uu____11419 -> true
                              | uu____11422 -> false)) in
                    match uu____11411 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11426 -> should_delta) in
               (log cfg
                  (fun uu____11434  ->
                     let uu____11435 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11436 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____11437 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11435 uu____11436 uu____11437);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack1 t1
                else
                  (let r_env =
                     let uu____11440 = FStar_Syntax_Syntax.range_of_fv f in
                     FStar_TypeChecker_Env.set_range cfg.tcenv uu____11440 in
                   let uu____11441 =
                     FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                       r_env
                       (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   match uu____11441 with
                   | FStar_Pervasives_Native.None  ->
                       (log cfg
                          (fun uu____11454  ->
                             FStar_Util.print "Tm_fvar case 2\n" []);
                        rebuild cfg env stack1 t1)
                   | FStar_Pervasives_Native.Some (us,t2) ->
                       (log cfg
                          (fun uu____11465  ->
                             let uu____11466 =
                               FStar_Syntax_Print.term_to_string t0 in
                             let uu____11467 =
                               FStar_Syntax_Print.term_to_string t2 in
                             FStar_Util.print2 ">>> Unfolded %s to %s\n"
                               uu____11466 uu____11467);
                        (let t3 =
                           let uu____11469 =
                             FStar_All.pipe_right cfg.steps
                               (FStar_List.contains
                                  (UnfoldUntil
                                     FStar_Syntax_Syntax.Delta_constant)) in
                           if uu____11469
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
                           | (UnivArgs (us',uu____11479))::stack2 ->
                               let env1 =
                                 FStar_All.pipe_right us'
                                   (FStar_List.fold_left
                                      (fun env1  ->
                                         fun u  -> (Univ u) :: env1) env) in
                               norm cfg env1 stack2 t3
                           | uu____11502 when
                               FStar_All.pipe_right cfg.steps
                                 (FStar_List.contains EraseUniverses)
                               -> norm cfg env stack1 t3
                           | uu____11503 ->
                               let uu____11504 =
                                 let uu____11505 =
                                   FStar_Syntax_Print.lid_to_string
                                     (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                 FStar_Util.format1
                                   "Impossible: missing universe instantiation on %s"
                                   uu____11505 in
                               failwith uu____11504
                         else norm cfg env stack1 t3))))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11508 = lookup_bvar env x in
               (match uu____11508 with
                | Univ uu____11509 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11534 = FStar_ST.op_Bang r in
                      (match uu____11534 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11635  ->
                                 let uu____11636 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____11637 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11636
                                   uu____11637);
                            (let uu____11638 =
                               let uu____11639 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____11639.FStar_Syntax_Syntax.n in
                             match uu____11638 with
                             | FStar_Syntax_Syntax.Tm_abs uu____11642 ->
                                 norm cfg env2 stack1 t'
                             | uu____11659 -> rebuild cfg env2 stack1 t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____11711)::uu____11712 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11721)::uu____11722 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11732,uu____11733))::stack_rest ->
                    (match c with
                     | Univ uu____11737 -> norm cfg (c :: env) stack_rest t1
                     | uu____11738 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____11743::[] ->
                              (log cfg
                                 (fun uu____11759  ->
                                    let uu____11760 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11760);
                               norm cfg (c :: env) stack_rest body)
                          | uu____11761::tl1 ->
                              (log cfg
                                 (fun uu____11780  ->
                                    let uu____11781 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11781);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___210_11811 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___210_11811.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____11896  ->
                          let uu____11897 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11897);
                     norm cfg env stack2 t1)
                | (Debug uu____11898)::uu____11899 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11906 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11906
                    else
                      (let uu____11908 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11908 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11932  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11948 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11948
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11958 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11958)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___211_11963 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___211_11963.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___211_11963.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11964 -> lopt in
                           (log cfg
                              (fun uu____11970  ->
                                 let uu____11971 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11971);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___212_11984 = cfg in
                               let uu____11985 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___212_11984.steps);
                                 tcenv = (uu___212_11984.tcenv);
                                 delta_level = (uu___212_11984.delta_level);
                                 primitive_steps = uu____11985
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____11994)::uu____11995 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12002 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12002
                    else
                      (let uu____12004 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12004 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12028  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12044 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12044
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12054 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12054)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___211_12059 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___211_12059.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___211_12059.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12060 -> lopt in
                           (log cfg
                              (fun uu____12066  ->
                                 let uu____12067 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12067);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___212_12080 = cfg in
                               let uu____12081 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___212_12080.steps);
                                 tcenv = (uu___212_12080.tcenv);
                                 delta_level = (uu___212_12080.delta_level);
                                 primitive_steps = uu____12081
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____12090)::uu____12091 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12102 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12102
                    else
                      (let uu____12104 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12104 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12128  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12144 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12144
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12154 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12154)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___211_12159 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___211_12159.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___211_12159.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12160 -> lopt in
                           (log cfg
                              (fun uu____12166  ->
                                 let uu____12167 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12167);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___212_12180 = cfg in
                               let uu____12181 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___212_12180.steps);
                                 tcenv = (uu___212_12180.tcenv);
                                 delta_level = (uu___212_12180.delta_level);
                                 primitive_steps = uu____12181
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____12190)::uu____12191 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12200 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12200
                    else
                      (let uu____12202 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12202 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12226  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12242 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12242
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12252 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12252)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___211_12257 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___211_12257.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___211_12257.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12258 -> lopt in
                           (log cfg
                              (fun uu____12264  ->
                                 let uu____12265 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12265);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___212_12278 = cfg in
                               let uu____12279 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___212_12278.steps);
                                 tcenv = (uu___212_12278.tcenv);
                                 delta_level = (uu___212_12278.delta_level);
                                 primitive_steps = uu____12279
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____12288)::uu____12289 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12304 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12304
                    else
                      (let uu____12306 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12306 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12330  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12346 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12346
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12356 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12356)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___211_12361 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___211_12361.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___211_12361.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12362 -> lopt in
                           (log cfg
                              (fun uu____12368  ->
                                 let uu____12369 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12369);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___212_12382 = cfg in
                               let uu____12383 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___212_12382.steps);
                                 tcenv = (uu___212_12382.tcenv);
                                 delta_level = (uu___212_12382.delta_level);
                                 primitive_steps = uu____12383
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12392 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12392
                    else
                      (let uu____12394 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12394 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12418  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12434 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12434
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12444 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12444)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___211_12449 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___211_12449.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___211_12449.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12450 -> lopt in
                           (log cfg
                              (fun uu____12456  ->
                                 let uu____12457 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12457);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___212_12470 = cfg in
                               let uu____12471 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___212_12470.steps);
                                 tcenv = (uu___212_12470.tcenv);
                                 delta_level = (uu___212_12470.delta_level);
                                 primitive_steps = uu____12471
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
                      (fun uu____12518  ->
                         fun stack2  ->
                           match uu____12518 with
                           | (a,aq) ->
                               let uu____12530 =
                                 let uu____12531 =
                                   let uu____12538 =
                                     let uu____12539 =
                                       let uu____12558 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____12558, false) in
                                     Clos uu____12539 in
                                   (uu____12538, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____12531 in
                               uu____12530 :: stack2) args) in
               (log cfg
                  (fun uu____12610  ->
                     let uu____12611 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12611);
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
                             ((let uu___213_12635 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___213_12635.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___213_12635.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____12636 ->
                      let uu____12641 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12641)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____12644 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____12644 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____12669 =
                          let uu____12670 =
                            let uu____12677 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___214_12679 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___214_12679.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___214_12679.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12677) in
                          FStar_Syntax_Syntax.Tm_refine uu____12670 in
                        mk uu____12669 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____12698 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____12698
               else
                 (let uu____12700 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____12700 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12708 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12720  -> Dummy :: env1) env) in
                        norm_comp cfg uu____12708 c1 in
                      let t2 =
                        let uu____12730 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____12730 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____12789)::uu____12790 -> norm cfg env stack1 t11
                | (Arg uu____12799)::uu____12800 -> norm cfg env stack1 t11
                | (App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____12809;
                       FStar_Syntax_Syntax.vars = uu____12810;_},uu____12811,uu____12812))::uu____12813
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____12820)::uu____12821 ->
                    norm cfg env stack1 t11
                | uu____12830 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____12834  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____12851 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____12851
                        | FStar_Util.Inr c ->
                            let uu____12859 = norm_comp cfg env c in
                            FStar_Util.Inr uu____12859 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____12865 =
                        let uu____12866 =
                          let uu____12867 =
                            let uu____12894 = FStar_Syntax_Util.unascribe t12 in
                            (uu____12894, (tc1, tacopt1), l) in
                          FStar_Syntax_Syntax.Tm_ascribed uu____12867 in
                        mk uu____12866 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____12865)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____12970,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____12971;
                               FStar_Syntax_Syntax.lbunivs = uu____12972;
                               FStar_Syntax_Syntax.lbtyp = uu____12973;
                               FStar_Syntax_Syntax.lbeff = uu____12974;
                               FStar_Syntax_Syntax.lbdef = uu____12975;_}::uu____12976),uu____12977)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____13013 =
                 (let uu____13016 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____13016) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____13018 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____13018))) in
               if uu____13013
               then
                 let env1 =
                   let uu____13022 =
                     let uu____13023 =
                       let uu____13042 =
                         FStar_Util.mk_ref FStar_Pervasives_Native.None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____13042,
                         false) in
                     Clos uu____13023 in
                   uu____13022 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____13094 =
                    let uu____13099 =
                      let uu____13100 =
                        let uu____13101 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____13101
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____13100] in
                    FStar_Syntax_Subst.open_term uu____13099 body in
                  match uu____13094 with
                  | (bs,body1) ->
                      let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                      let lbname =
                        let x =
                          let uu____13115 = FStar_List.hd bs in
                          FStar_Pervasives_Native.fst uu____13115 in
                        FStar_Util.Inl
                          (let uu___215_13125 = x in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___215_13125.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___215_13125.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = ty
                           }) in
                      let lb1 =
                        let uu___216_13127 = lb in
                        let uu____13128 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = lbname;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___216_13127.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = ty;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___216_13127.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____13128
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____13145  -> Dummy :: env1)
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
               let uu____13168 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____13168 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____13204 =
                               let uu___217_13205 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___217_13205.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___217_13205.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____13204 in
                           let uu____13206 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____13206 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____13226 =
                                   FStar_List.map (fun uu____13230  -> Dummy)
                                     lbs1 in
                                 let uu____13231 =
                                   let uu____13234 =
                                     FStar_List.map
                                       (fun uu____13242  -> Dummy) xs1 in
                                   FStar_List.append uu____13234 env in
                                 FStar_List.append uu____13226 uu____13231 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13254 =
                                       let uu___218_13255 = rc in
                                       let uu____13256 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___218_13255.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13256;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___218_13255.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____13254
                                 | uu____13263 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___219_13267 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___219_13267.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___219_13267.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____13271 =
                        FStar_List.map (fun uu____13275  -> Dummy) lbs2 in
                      FStar_List.append uu____13271 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____13277 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____13277 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___220_13293 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___220_13293.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___220_13293.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____13320 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____13320
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13339 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13390  ->
                        match uu____13390 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____13463 =
                                let uu___221_13464 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___221_13464.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___221_13464.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____13463 in
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
               (match uu____13339 with
                | (rec_env,memos,uu____13592) ->
                    let uu____13621 =
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
                             let uu____14086 =
                               let uu____14087 =
                                 let uu____14106 =
                                   FStar_Util.mk_ref
                                     FStar_Pervasives_Native.None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____14106, false) in
                               Clos uu____14087 in
                             uu____14086 :: env1)
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
                             FStar_Syntax_Syntax.pos = uu____14174;
                             FStar_Syntax_Syntax.vars = uu____14175;_},uu____14176,uu____14177))::uu____14178
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____14185 -> false in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____14195 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____14195
                        then
                          let uu___222_14196 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___222_14196.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps =
                              (uu___222_14196.primitive_steps)
                          }
                        else
                          (let uu___223_14198 = cfg in
                           {
                             steps =
                               (FStar_List.append [Exclude Zeta] cfg.steps);
                             tcenv = (uu___223_14198.tcenv);
                             delta_level = (uu___223_14198.delta_level);
                             primitive_steps =
                               (uu___223_14198.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____14200 =
                         let uu____14201 = FStar_Syntax_Subst.compress head1 in
                         uu____14201.FStar_Syntax_Syntax.n in
                       match uu____14200 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____14219 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____14219 with
                            | (uu____14220,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____14226 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____14234 =
                                         let uu____14235 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____14235.FStar_Syntax_Syntax.n in
                                       match uu____14234 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____14241,uu____14242))
                                           ->
                                           let uu____14251 =
                                             let uu____14252 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____14252.FStar_Syntax_Syntax.n in
                                           (match uu____14251 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____14258,msrc,uu____14260))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____14269 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14269
                                            | uu____14270 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____14271 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____14272 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____14272 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___224_14277 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___224_14277.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___224_14277.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___224_14277.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____14278 =
                                            FStar_List.tl stack1 in
                                          let uu____14279 =
                                            let uu____14280 =
                                              let uu____14283 =
                                                let uu____14284 =
                                                  let uu____14297 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____14297) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____14284 in
                                              FStar_Syntax_Syntax.mk
                                                uu____14283 in
                                            uu____14280
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____14278
                                            uu____14279
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____14313 =
                                            let uu____14314 = is_return body in
                                            match uu____14314 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____14318;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____14319;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____14324 -> false in
                                          if uu____14313
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
                                               let uu____14348 =
                                                 let uu____14351 =
                                                   let uu____14352 =
                                                     let uu____14369 =
                                                       let uu____14372 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____14372] in
                                                     (uu____14369, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc)) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____14352 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____14351 in
                                               uu____14348
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____14388 =
                                                 let uu____14389 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____14389.FStar_Syntax_Syntax.n in
                                               match uu____14388 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____14395::uu____14396::[])
                                                   ->
                                                   let uu____14403 =
                                                     let uu____14406 =
                                                       let uu____14407 =
                                                         let uu____14414 =
                                                           let uu____14417 =
                                                             let uu____14418
                                                               =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____14418 in
                                                           let uu____14419 =
                                                             let uu____14422
                                                               =
                                                               let uu____14423
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____14423 in
                                                             [uu____14422] in
                                                           uu____14417 ::
                                                             uu____14419 in
                                                         (bind1, uu____14414) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____14407 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____14406 in
                                                   uu____14403
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____14431 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____14437 =
                                                 let uu____14440 =
                                                   let uu____14441 =
                                                     let uu____14456 =
                                                       let uu____14459 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____14460 =
                                                         let uu____14463 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____14464 =
                                                           let uu____14467 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____14468 =
                                                             let uu____14471
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____14472
                                                               =
                                                               let uu____14475
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____14476
                                                                 =
                                                                 let uu____14479
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____14479] in
                                                               uu____14475 ::
                                                                 uu____14476 in
                                                             uu____14471 ::
                                                               uu____14472 in
                                                           uu____14467 ::
                                                             uu____14468 in
                                                         uu____14463 ::
                                                           uu____14464 in
                                                       uu____14459 ::
                                                         uu____14460 in
                                                     (bind_inst, uu____14456) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____14441 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____14440 in
                                               uu____14437
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____14487 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____14487 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____14511 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____14511 with
                            | (uu____14512,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____14541 =
                                        let uu____14542 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____14542.FStar_Syntax_Syntax.n in
                                      match uu____14541 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____14548) -> t4
                                      | uu____14553 -> head2 in
                                    let uu____14554 =
                                      let uu____14555 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____14555.FStar_Syntax_Syntax.n in
                                    match uu____14554 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____14561 ->
                                        FStar_Pervasives_Native.None in
                                  let uu____14562 = maybe_extract_fv head2 in
                                  match uu____14562 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____14572 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____14572
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____14577 =
                                          maybe_extract_fv head3 in
                                        match uu____14577 with
                                        | FStar_Pervasives_Native.Some
                                            uu____14582 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____14583 ->
                                            FStar_Pervasives_Native.Some
                                              false in
                                      (head3, action_unfolded)
                                  | uu____14588 ->
                                      (head2, FStar_Pervasives_Native.None) in
                                ((let is_arg_impure uu____14603 =
                                    match uu____14603 with
                                    | (e,q) ->
                                        let uu____14610 =
                                          let uu____14611 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____14611.FStar_Syntax_Syntax.n in
                                        (match uu____14610 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____14626 -> false) in
                                  let uu____14627 =
                                    let uu____14628 =
                                      let uu____14635 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____14635 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____14628 in
                                  if uu____14627
                                  then
                                    let uu____14640 =
                                      let uu____14641 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____14641 in
                                    failwith uu____14640
                                  else ());
                                 (let uu____14643 =
                                    maybe_unfold_action head_app in
                                  match uu____14643 with
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
                                      let uu____14682 = FStar_List.tl stack1 in
                                      norm cfg env uu____14682 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____14696 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____14696 in
                           let uu____14697 = FStar_List.tl stack1 in
                           norm cfg env uu____14697 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____14818  ->
                                     match uu____14818 with
                                     | (pat,wopt,tm) ->
                                         let uu____14866 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____14866))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____14898 = FStar_List.tl stack1 in
                           norm cfg env uu____14898 tm
                       | uu____14899 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.pos = uu____14908;
                             FStar_Syntax_Syntax.vars = uu____14909;_},uu____14910,uu____14911))::uu____14912
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____14919 -> false in
                    if should_reify
                    then
                      let uu____14920 = FStar_List.tl stack1 in
                      let uu____14921 =
                        let uu____14922 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____14922 in
                      norm cfg env uu____14920 uu____14921
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____14925 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____14925
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___225_14934 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___225_14934.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___225_14934.primitive_steps)
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
                | uu____14936 ->
                    if FStar_List.contains Unmeta cfg.steps
                    then norm cfg env stack1 head1
                    else
                      (match stack1 with
                       | uu____14938::uu____14939 ->
                           (match m with
                            | FStar_Syntax_Syntax.Meta_labeled
                                (l,r,uu____14944) ->
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
                            | uu____14969 -> norm cfg env stack1 head1)
                       | [] ->
                           let head2 = norm cfg env [] head1 in
                           let m1 =
                             match m with
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let uu____14983 =
                                   norm_pattern_args cfg env args in
                                 FStar_Syntax_Syntax.Meta_pattern uu____14983
                             | uu____14994 -> m in
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
              let uu____15006 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____15006 with
              | (uu____15007,return_repr) ->
                  let return_inst =
                    let uu____15016 =
                      let uu____15017 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____15017.FStar_Syntax_Syntax.n in
                    match uu____15016 with
                    | FStar_Syntax_Syntax.Tm_uinst
                        (return_tm,uu____15023::[]) ->
                        let uu____15030 =
                          let uu____15033 =
                            let uu____15034 =
                              let uu____15041 =
                                let uu____15044 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____15044] in
                              (return_tm, uu____15041) in
                            FStar_Syntax_Syntax.Tm_uinst uu____15034 in
                          FStar_Syntax_Syntax.mk uu____15033 in
                        uu____15030 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____15052 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____15055 =
                    let uu____15058 =
                      let uu____15059 =
                        let uu____15074 =
                          let uu____15077 = FStar_Syntax_Syntax.as_arg t in
                          let uu____15078 =
                            let uu____15081 = FStar_Syntax_Syntax.as_arg e in
                            [uu____15081] in
                          uu____15077 :: uu____15078 in
                        (return_inst, uu____15074) in
                      FStar_Syntax_Syntax.Tm_app uu____15059 in
                    FStar_Syntax_Syntax.mk uu____15058 in
                  uu____15055 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____15090 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____15090 with
               | FStar_Pervasives_Native.None  ->
                   let uu____15093 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____15093
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____15094;
                     FStar_TypeChecker_Env.mtarget = uu____15095;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____15096;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____15107;
                     FStar_TypeChecker_Env.mtarget = uu____15108;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____15109;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____15127 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____15127)
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
                (fun uu____15183  ->
                   match uu____15183 with
                   | (a,imp) ->
                       let uu____15194 = norm cfg env [] a in
                       (uu____15194, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___226_15211 = comp1 in
            let uu____15214 =
              let uu____15215 =
                let uu____15224 = norm cfg env [] t in
                let uu____15225 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____15224, uu____15225) in
              FStar_Syntax_Syntax.Total uu____15215 in
            {
              FStar_Syntax_Syntax.n = uu____15214;
              FStar_Syntax_Syntax.pos =
                (uu___226_15211.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___226_15211.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___227_15240 = comp1 in
            let uu____15243 =
              let uu____15244 =
                let uu____15253 = norm cfg env [] t in
                let uu____15254 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____15253, uu____15254) in
              FStar_Syntax_Syntax.GTotal uu____15244 in
            {
              FStar_Syntax_Syntax.n = uu____15243;
              FStar_Syntax_Syntax.pos =
                (uu___227_15240.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___227_15240.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____15306  ->
                      match uu____15306 with
                      | (a,i) ->
                          let uu____15317 = norm cfg env [] a in
                          (uu____15317, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___180_15328  ->
                      match uu___180_15328 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____15332 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____15332
                      | f -> f)) in
            let uu___228_15336 = comp1 in
            let uu____15339 =
              let uu____15340 =
                let uu___229_15341 = ct in
                let uu____15342 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____15343 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____15346 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____15342;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___229_15341.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____15343;
                  FStar_Syntax_Syntax.effect_args = uu____15346;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____15340 in
            {
              FStar_Syntax_Syntax.n = uu____15339;
              FStar_Syntax_Syntax.pos =
                (uu___228_15336.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___228_15336.FStar_Syntax_Syntax.vars)
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
            (let uu___230_15364 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___230_15364.tcenv);
               delta_level = (uu___230_15364.delta_level);
               primitive_steps = (uu___230_15364.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____15369 = norm1 t in
          FStar_Syntax_Util.non_informative uu____15369 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____15372 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___231_15391 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.pos =
                (uu___231_15391.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___231_15391.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____15398 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____15398
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
                    let uu___232_15409 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___232_15409.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___232_15409.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___232_15409.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___233_15411 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___233_15411.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___233_15411.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___233_15411.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___233_15411.FStar_Syntax_Syntax.flags)
                    } in
              let uu___234_15412 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos =
                  (uu___234_15412.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___234_15412.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____15414 -> c
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____15417  ->
        match uu____15417 with
        | (x,imp) ->
            let uu____15420 =
              let uu___235_15421 = x in
              let uu____15422 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___235_15421.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___235_15421.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____15422
              } in
            (uu____15420, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____15428 =
          FStar_List.fold_left
            (fun uu____15446  ->
               fun b  ->
                 match uu____15446 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____15428 with | (nbs,uu____15474) -> FStar_List.rev nbs
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
            let uu____15490 =
              let uu___236_15491 = rc in
              let uu____15492 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___236_15491.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____15492;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___236_15491.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____15490
        | uu____15499 -> lopt
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
              ((let uu____15512 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____15512
                then
                  let time_now = FStar_Util.now () in
                  let uu____15514 =
                    let uu____15515 =
                      let uu____15516 =
                        FStar_Util.time_diff time_then time_now in
                      FStar_Pervasives_Native.snd uu____15516 in
                    FStar_Util.string_of_int uu____15515 in
                  let uu____15521 = FStar_Syntax_Print.term_to_string tm in
                  let uu____15522 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                    uu____15514 uu____15521 uu____15522
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___237_15540 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___237_15540.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____15633  ->
                    let uu____15634 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____15634);
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
              let uu____15670 =
                let uu___238_15671 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___238_15671.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___238_15671.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____15670
          | (Arg (Univ uu____15672,uu____15673,uu____15674))::uu____15675 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____15678,uu____15679))::uu____15680 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____15696),aq,r))::stack2 ->
              (log cfg
                 (fun uu____15725  ->
                    let uu____15726 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____15726);
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
                 (let uu____15736 = FStar_ST.op_Bang m in
                  match uu____15736 with
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
                  | FStar_Pervasives_Native.Some (uu____15856,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq)
                          FStar_Pervasives_Native.None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 =
                FStar_Syntax_Syntax.extend_app head1 (t, aq)
                  FStar_Pervasives_Native.None r in
              let uu____15880 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____15880
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____15890  ->
                    let uu____15891 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____15891);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____15896 =
                  log cfg
                    (fun uu____15901  ->
                       let uu____15902 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____15903 =
                         let uu____15904 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____15921  ->
                                   match uu____15921 with
                                   | (p,uu____15931,uu____15932) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____15904
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____15902 uu____15903);
                  (let whnf1 = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___181_15949  ->
                               match uu___181_15949 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____15950 -> false)) in
                     let steps' =
                       let uu____15954 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____15954
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___239_15958 = cfg in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___239_15958.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___239_15958.primitive_steps)
                     } in
                   let norm_or_whnf env2 t1 =
                     if whnf1
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____16002 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____16025 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____16091  ->
                                   fun uu____16092  ->
                                     match (uu____16091, uu____16092) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____16195 = norm_pat env3 p1 in
                                         (match uu____16195 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____16025 with
                          | (pats1,env3) ->
                              ((let uu___240_16297 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.p =
                                    (uu___240_16297.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___241_16316 = x in
                           let uu____16317 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___241_16316.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___241_16316.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16317
                           } in
                         ((let uu___242_16325 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.p =
                               (uu___242_16325.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___243_16330 = x in
                           let uu____16331 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___243_16330.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___243_16330.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16331
                           } in
                         ((let uu___244_16339 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.p =
                               (uu___244_16339.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___245_16349 = x in
                           let uu____16350 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___245_16349.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___245_16349.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16350
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___246_16359 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.p =
                               (uu___246_16359.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf1 -> branches
                     | uu____16363 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____16377 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____16377 with
                                 | (p,wopt,e) ->
                                     let uu____16397 = norm_pat env1 p in
                                     (match uu____16397 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Pervasives_Native.Some w
                                                ->
                                                let uu____16428 =
                                                  norm_or_whnf env2 w in
                                                FStar_Pervasives_Native.Some
                                                  uu____16428 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____16434 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____16434) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____16444) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____16449 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____16450;
                        FStar_Syntax_Syntax.fv_delta = uu____16451;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Data_ctor );_}
                      -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____16452;
                        FStar_Syntax_Syntax.fv_delta = uu____16453;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Record_ctor uu____16454);_}
                      -> true
                  | uu____16461 -> false in
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
                  let uu____16590 =
                    FStar_Syntax_Util.head_and_args scrutinee1 in
                  match uu____16590 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var uu____16639 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_wild uu____16642 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____16645 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee1.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____16664 ->
                                let uu____16665 =
                                  let uu____16666 = is_cons head1 in
                                  Prims.op_Negation uu____16666 in
                                FStar_Util.Inr uu____16665)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____16687 =
                             let uu____16688 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____16688.FStar_Syntax_Syntax.n in
                           (match uu____16687 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____16698 ->
                                let uu____16699 =
                                  let uu____16700 = is_cons head1 in
                                  Prims.op_Negation uu____16700 in
                                FStar_Util.Inr uu____16699))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____16753)::rest_a,(p1,uu____16756)::rest_p) ->
                      let uu____16800 = matches_pat t1 p1 in
                      (match uu____16800 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____16825 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____16927 = matches_pat scrutinee1 p1 in
                      (match uu____16927 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____16947  ->
                                 let uu____16948 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____16949 =
                                   let uu____16950 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____16950
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____16948 uu____16949);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____16967 =
                                        let uu____16968 =
                                          let uu____16987 =
                                            FStar_Util.mk_ref
                                              (FStar_Pervasives_Native.Some
                                                 ([], t1)) in
                                          ([], t1, uu____16987, false) in
                                        Clos uu____16968 in
                                      uu____16967 :: env2) env1 s in
                             let uu____17040 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____17040))) in
                let uu____17041 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____17041
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___182_17064  ->
                match uu___182_17064 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____17068 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____17074 -> d in
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
            let uu___247_17103 = config s e in
            {
              steps = (uu___247_17103.steps);
              tcenv = (uu___247_17103.tcenv);
              delta_level = (uu___247_17103.delta_level);
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
      fun t  -> let uu____17128 = config s e in norm_comp uu____17128 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____17137 = config [] env in norm_universe uu____17137 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let uu____17146 = config [] env in ghost_to_pure_aux uu____17146 [] c
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
        let uu____17160 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____17160 in
      let uu____17161 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____17161
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___248_17163 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___248_17163.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___248_17163.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____17166  ->
                    let uu____17167 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____17167))
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
            ((let uu____17186 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____17186);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____17199 = config [AllowUnboundUniverses] env in
          norm_comp uu____17199 [] c
        with
        | e ->
            ((let uu____17206 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____17206);
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
                   let uu____17246 =
                     let uu____17247 =
                       let uu____17254 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____17254) in
                     FStar_Syntax_Syntax.Tm_refine uu____17247 in
                   mk uu____17246 t01.FStar_Syntax_Syntax.pos
               | uu____17259 -> t2)
          | uu____17260 -> t2 in
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
        let uu____17312 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____17312 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____17341 ->
                 let uu____17348 = FStar_Syntax_Util.abs_formals e in
                 (match uu____17348 with
                  | (actuals,uu____17358,uu____17359) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____17373 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____17373 with
                         | (binders,args) ->
                             let uu____17390 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____17390
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
      | uu____17400 ->
          let uu____17401 = FStar_Syntax_Util.head_and_args t in
          (match uu____17401 with
           | (head1,args) ->
               let uu____17438 =
                 let uu____17439 = FStar_Syntax_Subst.compress head1 in
                 uu____17439.FStar_Syntax_Syntax.n in
               (match uu____17438 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____17442,thead) ->
                    let uu____17468 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____17468 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____17510 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___253_17518 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___253_17518.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___253_17518.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___253_17518.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___253_17518.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___253_17518.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___253_17518.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___253_17518.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___253_17518.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___253_17518.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___253_17518.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___253_17518.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___253_17518.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___253_17518.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___253_17518.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___253_17518.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___253_17518.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___253_17518.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___253_17518.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___253_17518.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___253_17518.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___253_17518.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___253_17518.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___253_17518.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___253_17518.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___253_17518.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___253_17518.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___253_17518.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___253_17518.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___253_17518.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___253_17518.FStar_TypeChecker_Env.dsenv)
                                 }) t in
                            match uu____17510 with
                            | (uu____17519,ty,uu____17521) ->
                                eta_expand_with_type env t ty))
                | uu____17522 ->
                    let uu____17523 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___254_17531 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___254_17531.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___254_17531.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___254_17531.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___254_17531.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___254_17531.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___254_17531.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___254_17531.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___254_17531.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___254_17531.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___254_17531.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___254_17531.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___254_17531.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___254_17531.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___254_17531.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___254_17531.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___254_17531.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___254_17531.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___254_17531.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___254_17531.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___254_17531.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___254_17531.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___254_17531.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___254_17531.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___254_17531.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___254_17531.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___254_17531.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___254_17531.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___254_17531.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___254_17531.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___254_17531.FStar_TypeChecker_Env.dsenv)
                         }) t in
                    (match uu____17523 with
                     | (uu____17532,ty,uu____17534) ->
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
            | (uu____17612,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____17618,FStar_Util.Inl t) ->
                let uu____17624 =
                  let uu____17627 =
                    let uu____17628 =
                      let uu____17641 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____17641) in
                    FStar_Syntax_Syntax.Tm_arrow uu____17628 in
                  FStar_Syntax_Syntax.mk uu____17627 in
                uu____17624 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____17645 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____17645 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____17672 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____17727 ->
                    let uu____17728 =
                      let uu____17737 =
                        let uu____17738 = FStar_Syntax_Subst.compress t3 in
                        uu____17738.FStar_Syntax_Syntax.n in
                      (uu____17737, tc) in
                    (match uu____17728 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____17763) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____17800) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____17839,FStar_Util.Inl uu____17840) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____17863 -> failwith "Impossible") in
              (match uu____17672 with
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
          let uu____17972 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____17972 with
          | (univ_names1,binders1,tc) ->
              let uu____18030 = FStar_Util.left tc in
              (univ_names1, binders1, uu____18030)
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
          let uu____18069 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____18069 with
          | (univ_names1,binders1,tc) ->
              let uu____18129 = FStar_Util.right tc in
              (univ_names1, binders1, uu____18129)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____18164 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____18164 with
           | (univ_names1,binders1,typ1) ->
               let uu___255_18192 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___255_18192.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___255_18192.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___255_18192.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___255_18192.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___256_18213 = s in
          let uu____18214 =
            let uu____18215 =
              let uu____18224 = FStar_List.map (elim_uvars env) sigs in
              (uu____18224, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____18215 in
          {
            FStar_Syntax_Syntax.sigel = uu____18214;
            FStar_Syntax_Syntax.sigrng =
              (uu___256_18213.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___256_18213.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___256_18213.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___256_18213.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____18241 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____18241 with
           | (univ_names1,uu____18259,typ1) ->
               let uu___257_18273 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___257_18273.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___257_18273.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___257_18273.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___257_18273.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____18279 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____18279 with
           | (univ_names1,uu____18297,typ1) ->
               let uu___258_18311 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___258_18311.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___258_18311.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___258_18311.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___258_18311.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____18345 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____18345 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____18368 =
                            let uu____18369 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____18369 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____18368 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___259_18372 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___259_18372.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___259_18372.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___260_18373 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___260_18373.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___260_18373.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___260_18373.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___260_18373.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___261_18385 = s in
          let uu____18386 =
            let uu____18387 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____18387 in
          {
            FStar_Syntax_Syntax.sigel = uu____18386;
            FStar_Syntax_Syntax.sigrng =
              (uu___261_18385.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___261_18385.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___261_18385.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___261_18385.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____18391 = elim_uvars_aux_t env us [] t in
          (match uu____18391 with
           | (us1,uu____18409,t1) ->
               let uu___262_18423 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___262_18423.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___262_18423.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___262_18423.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___262_18423.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____18424 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____18426 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____18426 with
           | (univs1,binders,signature) ->
               let uu____18454 =
                 let uu____18463 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____18463 with
                 | (univs_opening,univs2) ->
                     let uu____18490 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____18490) in
               (match uu____18454 with
                | (univs_opening,univs_closing) ->
                    let uu____18507 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____18513 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____18514 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____18513, uu____18514) in
                    (match uu____18507 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____18536 =
                           match uu____18536 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____18554 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____18554 with
                                | (us1,t1) ->
                                    let uu____18565 =
                                      let uu____18570 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____18577 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____18570, uu____18577) in
                                    (match uu____18565 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____18590 =
                                           let uu____18595 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____18604 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____18595, uu____18604) in
                                         (match uu____18590 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____18620 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____18620 in
                                              let uu____18621 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____18621 with
                                               | (uu____18642,uu____18643,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____18658 =
                                                       let uu____18659 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____18659 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____18658 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____18664 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____18664 with
                           | (uu____18677,uu____18678,t1) -> t1 in
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
                             | uu____18738 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____18755 =
                               let uu____18756 =
                                 FStar_Syntax_Subst.compress body in
                               uu____18756.FStar_Syntax_Syntax.n in
                             match uu____18755 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____18815 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____18844 =
                               let uu____18845 =
                                 FStar_Syntax_Subst.compress t in
                               uu____18845.FStar_Syntax_Syntax.n in
                             match uu____18844 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____18866) ->
                                 let uu____18887 = destruct_action_body body in
                                 (match uu____18887 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____18932 ->
                                 let uu____18933 = destruct_action_body t in
                                 (match uu____18933 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____18982 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____18982 with
                           | (action_univs,t) ->
                               let uu____18991 = destruct_action_typ_templ t in
                               (match uu____18991 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___263_19032 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___263_19032.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___263_19032.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___264_19034 = ed in
                           let uu____19035 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____19036 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____19037 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____19038 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____19039 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____19040 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____19041 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____19042 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____19043 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____19044 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____19045 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____19046 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____19047 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____19048 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___264_19034.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___264_19034.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____19035;
                             FStar_Syntax_Syntax.bind_wp = uu____19036;
                             FStar_Syntax_Syntax.if_then_else = uu____19037;
                             FStar_Syntax_Syntax.ite_wp = uu____19038;
                             FStar_Syntax_Syntax.stronger = uu____19039;
                             FStar_Syntax_Syntax.close_wp = uu____19040;
                             FStar_Syntax_Syntax.assert_p = uu____19041;
                             FStar_Syntax_Syntax.assume_p = uu____19042;
                             FStar_Syntax_Syntax.null_wp = uu____19043;
                             FStar_Syntax_Syntax.trivial = uu____19044;
                             FStar_Syntax_Syntax.repr = uu____19045;
                             FStar_Syntax_Syntax.return_repr = uu____19046;
                             FStar_Syntax_Syntax.bind_repr = uu____19047;
                             FStar_Syntax_Syntax.actions = uu____19048
                           } in
                         let uu___265_19051 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___265_19051.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___265_19051.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___265_19051.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___265_19051.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___183_19068 =
            match uu___183_19068 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____19095 = elim_uvars_aux_t env us [] t in
                (match uu____19095 with
                 | (us1,uu____19119,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___266_19138 = sub_eff in
            let uu____19139 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____19142 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___266_19138.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___266_19138.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____19139;
              FStar_Syntax_Syntax.lift = uu____19142
            } in
          let uu___267_19145 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___267_19145.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___267_19145.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___267_19145.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___267_19145.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____19155 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____19155 with
           | (univ_names1,binders1,comp1) ->
               let uu___268_19189 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___268_19189.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___268_19189.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___268_19189.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___268_19189.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____19200 -> s