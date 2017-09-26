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
  fun uu___149_395  ->
    match uu___149_395 with
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
  fun uu___150_1740  ->
    match uu___150_1740 with
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
  fun uu___151_1847  ->
    match uu___151_1847 with | [] -> true | uu____1850 -> false
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
                           (let uu___169_3024 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___169_3024.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___169_3024.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____3018)) in
                  (match uu____2988 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___170_3040 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___170_3040.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___170_3040.FStar_Syntax_Syntax.lbeff);
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
                           (let uu___171_3123 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___171_3123.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___171_3123.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_43  -> FStar_Util.Inl _0_43)) in
                    let uu___172_3124 = lb in
                    let uu____3125 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___172_3124.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___172_3124.FStar_Syntax_Syntax.lbeff);
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
                                   ((let uu___173_3582 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___173_3582.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___174_3601 = x in
                                let uu____3602 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___174_3601.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___174_3601.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3602
                                } in
                              ((let uu___175_3610 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___175_3610.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___176_3615 = x in
                                let uu____3616 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___176_3615.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___176_3615.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3616
                                } in
                              ((let uu___177_3624 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___177_3624.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___178_3634 = x in
                                let uu____3635 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___178_3634.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___178_3634.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3635
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___179_3644 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___179_3644.FStar_Syntax_Syntax.p)
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
                          let uu___180_4010 = b in
                          let uu____4011 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___180_4010.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___180_4010.FStar_Syntax_Syntax.index);
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
                        (fun uu___152_4148  ->
                           match uu___152_4148 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____4152 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____4152
                           | f -> f)) in
                 let uu____4156 =
                   let uu___181_4157 = c1 in
                   let uu____4158 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____4158;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___181_4157.FStar_Syntax_Syntax.effect_name);
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
         (fun uu___153_4168  ->
            match uu___153_4168 with
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
                   (fun uu___154_4192  ->
                      match uu___154_4192 with
                      | FStar_Syntax_Syntax.DECREASES uu____4193 -> false
                      | uu____4196 -> true)) in
            let rc1 =
              let uu___182_4198 = rc in
              let uu____4199 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___182_4198.FStar_Syntax_Syntax.residual_effect);
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
         | uu____4468 -> FStar_Pervasives_Native.None) in
  let arg_as_string uu____4478 =
    match uu____4478 with
    | (a,uu____4486) ->
        let uu____4489 =
          let uu____4490 = FStar_Syntax_Subst.compress a in
          uu____4490.FStar_Syntax_Syntax.n in
        (match uu____4489 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____4496)) -> FStar_Pervasives_Native.Some s
         | uu____4497 -> FStar_Pervasives_Native.None) in
  let arg_as_list f uu____4523 =
    match uu____4523 with
    | (a,uu____4537) ->
        let rec sequence l =
          match l with
          | [] -> FStar_Pervasives_Native.Some []
          | (FStar_Pervasives_Native.None )::uu____4566 ->
              FStar_Pervasives_Native.None
          | (FStar_Pervasives_Native.Some x)::xs ->
              let uu____4583 = sequence xs in
              (match uu____4583 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some xs' ->
                   FStar_Pervasives_Native.Some (x :: xs')) in
        let uu____4603 = FStar_Syntax_Util.list_elements a in
        (match uu____4603 with
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some elts ->
             let uu____4621 =
               FStar_List.map
                 (fun x  ->
                    let uu____4631 = FStar_Syntax_Syntax.as_arg x in
                    f uu____4631) elts in
             sequence uu____4621) in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4669 = f a in FStar_Pervasives_Native.Some uu____4669
    | uu____4670 -> FStar_Pervasives_Native.None in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4720 = f a0 a1 in FStar_Pervasives_Native.Some uu____4720
    | uu____4721 -> FStar_Pervasives_Native.None in
  let unary_op as_a f r args =
    let uu____4770 = FStar_List.map as_a args in lift_unary (f r) uu____4770 in
  let binary_op as_a f r args =
    let uu____4826 = FStar_List.map as_a args in lift_binary (f r) uu____4826 in
  let as_primitive_step uu____4850 =
    match uu____4850 with
    | (l,arity,f) ->
        { name = l; arity; strong_reduction_ok = true; interpretation = f } in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  -> fun x  -> let uu____4898 = f x in int_as_const r uu____4898) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  -> let uu____4926 = f x y in int_as_const r uu____4926) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  -> fun x  -> let uu____4947 = f x in bool_as_const r uu____4947) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  -> let uu____4975 = f x y in bool_as_const r uu____4975) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  -> let uu____5003 = f x y in string_as_const r uu____5003) in
  let list_of_string' rng s =
    let name l =
      let uu____5017 =
        let uu____5018 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____5018 in
      mk uu____5017 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____5052 =
      let uu____5055 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____5055 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____5052 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in int_as_const rng r in
  let string_concat' rng args =
    match args with
    | a1::a2::[] ->
        let uu____5130 = arg_as_string a1 in
        (match uu____5130 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5136 = arg_as_list arg_as_string a2 in
             (match uu____5136 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____5149 = string_as_const rng r in
                  FStar_Pervasives_Native.Some uu____5149
              | uu____5150 -> FStar_Pervasives_Native.None)
         | uu____5155 -> FStar_Pervasives_Native.None)
    | uu____5158 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____5172 = FStar_Util.string_of_int i in
    string_as_const rng uu____5172 in
  let string_of_bool1 rng b =
    string_as_const rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____5188 = FStar_Util.string_of_int i in
    string_as_const rng uu____5188 in
  let string_of_bool2 rng b =
    string_as_const rng (if b then "true" else "false") in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r in
  let range_of1 uu____5218 args =
    match args with
    | uu____5230::(t,uu____5232)::[] ->
        let uu____5261 = term_of_range t.FStar_Syntax_Syntax.pos in
        FStar_Pervasives_Native.Some uu____5261
    | uu____5266 -> FStar_Pervasives_Native.None in
  let set_range_of1 r args =
    match args with
    | uu____5304::(t,uu____5306)::({
                                     FStar_Syntax_Syntax.n =
                                       FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_range r1);
                                     FStar_Syntax_Syntax.pos = uu____5308;
                                     FStar_Syntax_Syntax.vars = uu____5309;_},uu____5310)::[]
        ->
        FStar_Pervasives_Native.Some
          (let uu___183_5352 = t in
           {
             FStar_Syntax_Syntax.n = (uu___183_5352.FStar_Syntax_Syntax.n);
             FStar_Syntax_Syntax.pos = r1;
             FStar_Syntax_Syntax.vars =
               (uu___183_5352.FStar_Syntax_Syntax.vars)
           })
    | uu____5355 -> FStar_Pervasives_Native.None in
  let mk_range1 r args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____5436 =
          let uu____5457 = arg_as_string fn in
          let uu____5460 = arg_as_int from_line in
          let uu____5463 = arg_as_int from_col in
          let uu____5466 = arg_as_int to_line in
          let uu____5469 = arg_as_int to_col in
          (uu____5457, uu____5460, uu____5463, uu____5466, uu____5469) in
        (match uu____5436 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r1 =
               let uu____5500 = FStar_Range.mk_pos from_l from_c in
               let uu____5501 = FStar_Range.mk_pos to_l to_c in
               FStar_Range.mk_range fn1 uu____5500 uu____5501 in
             let uu____5502 = term_of_range r1 in
             FStar_Pervasives_Native.Some uu____5502
         | uu____5507 -> FStar_Pervasives_Native.None)
    | uu____5528 -> FStar_Pervasives_Native.None in
  let decidable_eq neg rng args =
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) rng in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) rng in
    match args with
    | (_typ,uu____5558)::(a1,uu____5560)::(a2,uu____5562)::[] ->
        let uu____5599 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____5599 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____5612 -> FStar_Pervasives_Native.None)
    | uu____5613 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____5631 =
      let uu____5646 =
        let uu____5661 =
          let uu____5676 =
            let uu____5691 =
              let uu____5706 =
                let uu____5721 =
                  let uu____5736 =
                    let uu____5751 =
                      let uu____5766 =
                        let uu____5781 =
                          let uu____5796 =
                            let uu____5811 =
                              let uu____5826 =
                                let uu____5841 =
                                  let uu____5856 =
                                    let uu____5871 =
                                      let uu____5886 =
                                        let uu____5901 =
                                          let uu____5916 =
                                            let uu____5931 =
                                              let uu____5944 =
                                                FStar_Parser_Const.p2l
                                                  ["FStar";
                                                  "String";
                                                  "list_of_string"] in
                                              (uu____5944,
                                                (Prims.parse_int "1"),
                                                (unary_op arg_as_string
                                                   list_of_string')) in
                                            let uu____5951 =
                                              let uu____5966 =
                                                let uu____5979 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "string_of_list"] in
                                                (uu____5979,
                                                  (Prims.parse_int "1"),
                                                  (unary_op
                                                     (arg_as_list arg_as_char)
                                                     string_of_list')) in
                                              let uu____5988 =
                                                let uu____6003 =
                                                  let uu____6022 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "concat"] in
                                                  (uu____6022,
                                                    (Prims.parse_int "2"),
                                                    string_concat') in
                                                let uu____6035 =
                                                  let uu____6056 =
                                                    let uu____6077 =
                                                      FStar_Parser_Const.p2l
                                                        ["Prims"; "range_of"] in
                                                    (uu____6077,
                                                      (Prims.parse_int "2"),
                                                      range_of1) in
                                                  let uu____6092 =
                                                    let uu____6115 =
                                                      let uu____6136 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "set_range_of"] in
                                                      (uu____6136,
                                                        (Prims.parse_int "3"),
                                                        set_range_of1) in
                                                    let uu____6151 =
                                                      let uu____6174 =
                                                        let uu____6193 =
                                                          FStar_Parser_Const.p2l
                                                            ["Prims";
                                                            "mk_range"] in
                                                        (uu____6193,
                                                          (Prims.parse_int
                                                             "5"), mk_range1) in
                                                      [uu____6174] in
                                                    uu____6115 :: uu____6151 in
                                                  uu____6056 :: uu____6092 in
                                                uu____6003 :: uu____6035 in
                                              uu____5966 :: uu____5988 in
                                            uu____5931 :: uu____5951 in
                                          (FStar_Parser_Const.op_notEq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq true)) ::
                                            uu____5916 in
                                        (FStar_Parser_Const.op_Eq,
                                          (Prims.parse_int "3"),
                                          (decidable_eq false)) :: uu____5901 in
                                      (FStar_Parser_Const.string_compare,
                                        (Prims.parse_int "2"),
                                        (binary_op arg_as_string
                                           string_compare'))
                                        :: uu____5886 in
                                    (FStar_Parser_Const.string_of_bool_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_bool string_of_bool2))
                                      :: uu____5871 in
                                  (FStar_Parser_Const.string_of_int_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_int string_of_int2)) ::
                                    uu____5856 in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____5841 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5826 in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____5811 in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____5796 in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____5781 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____5766 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
                      :: uu____5751 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____5736 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____5721 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____5706 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____5691 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____5676 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____5661 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____5646 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____5631 in
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
      let uu____6800 =
        let uu____6801 =
          let uu____6802 = FStar_Syntax_Syntax.as_arg c in [uu____6802] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6801 in
      uu____6800 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____6837 =
              let uu____6850 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____6850, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____6869  ->
                        fun uu____6870  ->
                          match (uu____6869, uu____6870) with
                          | ((int_to_t1,x),(uu____6889,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____6899 =
              let uu____6914 =
                let uu____6927 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____6927, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____6946  ->
                          fun uu____6947  ->
                            match (uu____6946, uu____6947) with
                            | ((int_to_t1,x),(uu____6966,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____6976 =
                let uu____6991 =
                  let uu____7004 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____7004, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____7023  ->
                            fun uu____7024  ->
                              match (uu____7023, uu____7024) with
                              | ((int_to_t1,x),(uu____7043,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____6991] in
              uu____6914 :: uu____6976 in
            uu____6837 :: uu____6899)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop r args =
    match args with
    | (_typ,uu____7139)::(a1,uu____7141)::(a2,uu____7143)::[] ->
        let uu____7180 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____7180 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___184_7186 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___184_7186.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___184_7186.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___185_7190 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___185_7190.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___185_7190.FStar_Syntax_Syntax.vars)
                })
         | uu____7191 -> FStar_Pervasives_Native.None)
    | (_typ,uu____7193)::uu____7194::(a1,uu____7196)::(a2,uu____7198)::[] ->
        let uu____7247 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____7247 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___184_7253 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___184_7253.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___184_7253.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___185_7257 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___185_7257.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___185_7257.FStar_Syntax_Syntax.vars)
                })
         | uu____7258 -> FStar_Pervasives_Native.None)
    | uu____7259 -> failwith "Unexpected number of arguments" in
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
      let uu____7272 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops cfg.steps) in
      if uu____7272
      then tm
      else
        (let uu____7274 = FStar_Syntax_Util.head_and_args tm in
         match uu____7274 with
         | (head1,args) ->
             let uu____7311 =
               let uu____7312 = FStar_Syntax_Util.un_uinst head1 in
               uu____7312.FStar_Syntax_Syntax.n in
             (match uu____7311 with
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____7316 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps in
                  (match uu____7316 with
                   | FStar_Pervasives_Native.None  -> tm
                   | FStar_Pervasives_Native.Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then tm
                       else
                         (let uu____7329 =
                            prim_step.interpretation
                              head1.FStar_Syntax_Syntax.pos args in
                          match uu____7329 with
                          | FStar_Pervasives_Native.None  -> tm
                          | FStar_Pervasives_Native.Some reduced -> reduced))
              | uu____7333 -> tm))
let reduce_equality:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___186_7344 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___186_7344.tcenv);
           delta_level = (uu___186_7344.delta_level);
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
        let uu___187_7368 = t in
        {
          FStar_Syntax_Syntax.n = (uu___187_7368.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___187_7368.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid ->
            FStar_Pervasives_Native.Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid ->
            FStar_Pervasives_Native.Some false
        | uu____7385 -> FStar_Pervasives_Native.None in
      let simplify arg = ((simp_t (FStar_Pervasives_Native.fst arg)), arg) in
      let tm1 = reduce_primops cfg tm in
      let uu____7425 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps) in
      if uu____7425
      then tm1
      else
        (match tm1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.pos = uu____7428;
                     FStar_Syntax_Syntax.vars = uu____7429;_},uu____7430);
                FStar_Syntax_Syntax.pos = uu____7431;
                FStar_Syntax_Syntax.vars = uu____7432;_},args)
             ->
             let uu____7458 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
             if uu____7458
             then
               let uu____7459 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____7459 with
                | (FStar_Pervasives_Native.Some (true ),uu____7514)::
                    (uu____7515,(arg,uu____7517))::[] -> arg
                | (uu____7582,(arg,uu____7584))::(FStar_Pervasives_Native.Some
                                                  (true ),uu____7585)::[]
                    -> arg
                | (FStar_Pervasives_Native.Some (false ),uu____7650)::uu____7651::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____7714::(FStar_Pervasives_Native.Some (false
                               ),uu____7715)::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____7778 -> tm1)
             else
               (let uu____7794 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
                if uu____7794
                then
                  let uu____7795 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____7795 with
                  | (FStar_Pervasives_Native.Some (true ),uu____7850)::uu____7851::[]
                      -> w FStar_Syntax_Util.t_true
                  | uu____7914::(FStar_Pervasives_Native.Some (true
                                 ),uu____7915)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____7978)::
                      (uu____7979,(arg,uu____7981))::[] -> arg
                  | (uu____8046,(arg,uu____8048))::(FStar_Pervasives_Native.Some
                                                    (false ),uu____8049)::[]
                      -> arg
                  | uu____8114 -> tm1
                else
                  (let uu____8130 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.imp_lid in
                   if uu____8130
                   then
                     let uu____8131 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____8131 with
                     | uu____8186::(FStar_Pervasives_Native.Some (true
                                    ),uu____8187)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____8250)::uu____8251::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____8314)::
                         (uu____8315,(arg,uu____8317))::[] -> arg
                     | (uu____8382,(p,uu____8384))::(uu____8385,(q,uu____8387))::[]
                         ->
                         let uu____8452 = FStar_Syntax_Util.term_eq p q in
                         (if uu____8452
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____8454 -> tm1
                   else
                     (let uu____8470 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____8470
                      then
                        let uu____8471 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____8471 with
                        | (FStar_Pervasives_Native.Some (true ),uu____8526)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____8565)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____8604 -> tm1
                      else
                        (let uu____8620 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____8620
                         then
                           match args with
                           | (t,uu____8622)::[] ->
                               let uu____8639 =
                                 let uu____8640 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____8640.FStar_Syntax_Syntax.n in
                               (match uu____8639 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____8643::[],body,uu____8645) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____8672 -> tm1)
                                | uu____8675 -> tm1)
                           | (uu____8676,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____8677))::
                               (t,uu____8679)::[] ->
                               let uu____8718 =
                                 let uu____8719 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____8719.FStar_Syntax_Syntax.n in
                               (match uu____8718 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____8722::[],body,uu____8724) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____8751 -> tm1)
                                | uu____8754 -> tm1)
                           | uu____8755 -> tm1
                         else
                           (let uu____8765 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____8765
                            then
                              match args with
                              | (t,uu____8767)::[] ->
                                  let uu____8784 =
                                    let uu____8785 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____8785.FStar_Syntax_Syntax.n in
                                  (match uu____8784 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____8788::[],body,uu____8790) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____8817 -> tm1)
                                   | uu____8820 -> tm1)
                              | (uu____8821,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____8822))::
                                  (t,uu____8824)::[] ->
                                  let uu____8863 =
                                    let uu____8864 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____8864.FStar_Syntax_Syntax.n in
                                  (match uu____8863 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____8867::[],body,uu____8869) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____8896 -> tm1)
                                   | uu____8899 -> tm1)
                              | uu____8900 -> tm1
                            else reduce_equality cfg tm1)))))
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                FStar_Syntax_Syntax.pos = uu____8911;
                FStar_Syntax_Syntax.vars = uu____8912;_},args)
             ->
             let uu____8934 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
             if uu____8934
             then
               let uu____8935 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____8935 with
                | (FStar_Pervasives_Native.Some (true ),uu____8990)::
                    (uu____8991,(arg,uu____8993))::[] -> arg
                | (uu____9058,(arg,uu____9060))::(FStar_Pervasives_Native.Some
                                                  (true ),uu____9061)::[]
                    -> arg
                | (FStar_Pervasives_Native.Some (false ),uu____9126)::uu____9127::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____9190::(FStar_Pervasives_Native.Some (false
                               ),uu____9191)::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____9254 -> tm1)
             else
               (let uu____9270 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
                if uu____9270
                then
                  let uu____9271 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____9271 with
                  | (FStar_Pervasives_Native.Some (true ),uu____9326)::uu____9327::[]
                      -> w FStar_Syntax_Util.t_true
                  | uu____9390::(FStar_Pervasives_Native.Some (true
                                 ),uu____9391)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____9454)::
                      (uu____9455,(arg,uu____9457))::[] -> arg
                  | (uu____9522,(arg,uu____9524))::(FStar_Pervasives_Native.Some
                                                    (false ),uu____9525)::[]
                      -> arg
                  | uu____9590 -> tm1
                else
                  (let uu____9606 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.imp_lid in
                   if uu____9606
                   then
                     let uu____9607 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____9607 with
                     | uu____9662::(FStar_Pervasives_Native.Some (true
                                    ),uu____9663)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____9726)::uu____9727::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____9790)::
                         (uu____9791,(arg,uu____9793))::[] -> arg
                     | (uu____9858,(p,uu____9860))::(uu____9861,(q,uu____9863))::[]
                         ->
                         let uu____9928 = FStar_Syntax_Util.term_eq p q in
                         (if uu____9928
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____9930 -> tm1
                   else
                     (let uu____9946 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____9946
                      then
                        let uu____9947 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____9947 with
                        | (FStar_Pervasives_Native.Some (true ),uu____10002)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____10041)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____10080 -> tm1
                      else
                        (let uu____10096 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____10096
                         then
                           match args with
                           | (t,uu____10098)::[] ->
                               let uu____10115 =
                                 let uu____10116 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____10116.FStar_Syntax_Syntax.n in
                               (match uu____10115 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____10119::[],body,uu____10121) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____10148 -> tm1)
                                | uu____10151 -> tm1)
                           | (uu____10152,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____10153))::
                               (t,uu____10155)::[] ->
                               let uu____10194 =
                                 let uu____10195 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____10195.FStar_Syntax_Syntax.n in
                               (match uu____10194 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____10198::[],body,uu____10200) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____10227 -> tm1)
                                | uu____10230 -> tm1)
                           | uu____10231 -> tm1
                         else
                           (let uu____10241 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____10241
                            then
                              match args with
                              | (t,uu____10243)::[] ->
                                  let uu____10260 =
                                    let uu____10261 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____10261.FStar_Syntax_Syntax.n in
                                  (match uu____10260 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____10264::[],body,uu____10266) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____10293 -> tm1)
                                   | uu____10296 -> tm1)
                              | (uu____10297,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____10298))::
                                  (t,uu____10300)::[] ->
                                  let uu____10339 =
                                    let uu____10340 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____10340.FStar_Syntax_Syntax.n in
                                  (match uu____10339 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____10343::[],body,uu____10345) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____10372 -> tm1)
                                   | uu____10375 -> tm1)
                              | uu____10376 -> tm1
                            else reduce_equality cfg tm1)))))
         | uu____10386 -> tm1)
let is_norm_request:
  'Auu____10393 .
    FStar_Syntax_Syntax.term -> 'Auu____10393 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10406 =
        let uu____10413 =
          let uu____10414 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10414.FStar_Syntax_Syntax.n in
        (uu____10413, args) in
      match uu____10406 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10420::uu____10421::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10425::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10430::uu____10431::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10434 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___155_10446  ->
    match uu___155_10446 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.WHNF  -> [WHNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10452 =
          let uu____10455 =
            let uu____10456 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____10456 in
          [uu____10455] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10452
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____10475 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10475) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10513 =
          FStar_Syntax_Embeddings.unembed_list
            FStar_Syntax_Embeddings.unembed_norm_step s in
        FStar_All.pipe_left tr_norm_steps uu____10513 in
      match args with
      | uu____10526::(tm,uu____10528)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____10551)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____10566)::uu____10567::(tm,uu____10569)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____10609 =
              let uu____10612 = full_norm steps in parse_steps uu____10612 in
            Beta :: uu____10609 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____10621 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___156_10639  ->
    match uu___156_10639 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.pos = uu____10642;
           FStar_Syntax_Syntax.vars = uu____10643;_},uu____10644,uu____10645))::uu____10646
        -> true
    | uu____10653 -> false
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
            (fun uu____10788  ->
               let uu____10789 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____10790 = FStar_Syntax_Print.term_to_string t1 in
               let uu____10791 =
                 let uu____10792 =
                   let uu____10795 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____10795 in
                 stack_to_string uu____10792 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____10789
                 uu____10790 uu____10791);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____10818 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____10843 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____10860 =
                 let uu____10861 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____10862 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____10861 uu____10862 in
               failwith uu____10860
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____10863 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____10880 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____10881 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10882;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____10883;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10886;
                 FStar_Syntax_Syntax.fv_delta = uu____10887;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10888;
                 FStar_Syntax_Syntax.fv_delta = uu____10889;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____10890);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (FStar_Syntax_Util.is_fstar_tactics_embed hd1) ||
                 (FStar_Syntax_Util.is_fstar_tactics_by_tactic hd1)
               ->
               let args1 = closures_as_args_delayed cfg env args in
               let hd2 = closure_as_term cfg env hd1 in
               let t2 =
                 let uu___188_10932 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___188_10932.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___188_10932.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____10965 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____10965) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___189_10973 = cfg in
                 let uu____10974 =
                   FStar_List.filter
                     (fun uu___157_10977  ->
                        match uu___157_10977 with
                        | UnfoldOnly uu____10978 -> false
                        | NoDeltaSteps  -> false
                        | uu____10981 -> true) cfg.steps in
                 {
                   steps = uu____10974;
                   tcenv = (uu___189_10973.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___189_10973.primitive_steps)
                 } in
               let uu____10982 = get_norm_request (norm cfg' env []) args in
               (match uu____10982 with
                | (s,tm) ->
                    let delta_level =
                      let uu____10998 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___158_11003  ->
                                match uu___158_11003 with
                                | UnfoldUntil uu____11004 -> true
                                | UnfoldOnly uu____11005 -> true
                                | uu____11008 -> false)) in
                      if uu____10998
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___190_11013 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___190_11013.tcenv);
                        delta_level;
                        primitive_steps = (uu___190_11013.primitive_steps)
                      } in
                    let stack' =
                      let tail1 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let uu____11024 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____11024
                      then
                        let uu____11027 =
                          let uu____11028 =
                            let uu____11033 = FStar_Util.now () in
                            (t1, uu____11033) in
                          Debug uu____11028 in
                        uu____11027 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11035;
                  FStar_Syntax_Syntax.vars = uu____11036;_},a1::a2::rest)
               ->
               let uu____11084 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11084 with
                | (hd1,uu____11100) ->
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
                    (FStar_Const.Const_reflect uu____11165);
                  FStar_Syntax_Syntax.pos = uu____11166;
                  FStar_Syntax_Syntax.vars = uu____11167;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____11199 = FStar_List.tl stack1 in
               norm cfg env uu____11199 (FStar_Pervasives_Native.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11202;
                  FStar_Syntax_Syntax.vars = uu____11203;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____11235 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11235 with
                | (reify_head,uu____11251) ->
                    let a1 =
                      let uu____11273 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (FStar_Pervasives_Native.fst a) in
                      FStar_Syntax_Subst.compress uu____11273 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____11276);
                            FStar_Syntax_Syntax.pos = uu____11277;
                            FStar_Syntax_Syntax.vars = uu____11278;_},a2::[])
                         ->
                         norm cfg env stack1 (FStar_Pervasives_Native.fst a2)
                     | uu____11312 ->
                         let stack2 =
                           (App
                              (reify_head, FStar_Pervasives_Native.None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11322 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____11322
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11329 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11329
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____11332 =
                      let uu____11339 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11339, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11332 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___159_11353  ->
                         match uu___159_11353 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11356 =
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
                 if uu____11356
                 then false
                 else
                   (let uu____11358 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___160_11365  ->
                              match uu___160_11365 with
                              | UnfoldOnly uu____11366 -> true
                              | uu____11369 -> false)) in
                    match uu____11358 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11373 -> should_delta) in
               (log cfg
                  (fun uu____11381  ->
                     let uu____11382 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11383 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____11384 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11382 uu____11383 uu____11384);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack1 t1
                else
                  (let r_env =
                     let uu____11387 = FStar_Syntax_Syntax.range_of_fv f in
                     FStar_TypeChecker_Env.set_range cfg.tcenv uu____11387 in
                   let uu____11388 =
                     FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                       r_env
                       (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   match uu____11388 with
                   | FStar_Pervasives_Native.None  ->
                       (log cfg
                          (fun uu____11401  ->
                             FStar_Util.print "Tm_fvar case 2\n" []);
                        rebuild cfg env stack1 t1)
                   | FStar_Pervasives_Native.Some (us,t2) ->
                       (log cfg
                          (fun uu____11412  ->
                             let uu____11413 =
                               FStar_Syntax_Print.term_to_string t0 in
                             let uu____11414 =
                               FStar_Syntax_Print.term_to_string t2 in
                             FStar_Util.print2 ">>> Unfolded %s to %s\n"
                               uu____11413 uu____11414);
                        (let t3 =
                           let uu____11416 =
                             FStar_All.pipe_right cfg.steps
                               (FStar_List.contains
                                  (UnfoldUntil
                                     FStar_Syntax_Syntax.Delta_constant)) in
                           if uu____11416
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
                           | (UnivArgs (us',uu____11426))::stack2 ->
                               let env1 =
                                 FStar_All.pipe_right us'
                                   (FStar_List.fold_left
                                      (fun env1  ->
                                         fun u  -> (Univ u) :: env1) env) in
                               norm cfg env1 stack2 t3
                           | uu____11449 when
                               FStar_All.pipe_right cfg.steps
                                 (FStar_List.contains EraseUniverses)
                               -> norm cfg env stack1 t3
                           | uu____11450 ->
                               let uu____11451 =
                                 let uu____11452 =
                                   FStar_Syntax_Print.lid_to_string
                                     (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                 FStar_Util.format1
                                   "Impossible: missing universe instantiation on %s"
                                   uu____11452 in
                               failwith uu____11451
                         else norm cfg env stack1 t3))))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11455 = lookup_bvar env x in
               (match uu____11455 with
                | Univ uu____11456 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11481 = FStar_ST.op_Bang r in
                      (match uu____11481 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11562  ->
                                 let uu____11563 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____11564 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11563
                                   uu____11564);
                            (let uu____11565 =
                               let uu____11566 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____11566.FStar_Syntax_Syntax.n in
                             match uu____11565 with
                             | FStar_Syntax_Syntax.Tm_abs uu____11569 ->
                                 norm cfg env2 stack1 t'
                             | uu____11586 -> rebuild cfg env2 stack1 t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____11638)::uu____11639 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11648)::uu____11649 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11659,uu____11660))::stack_rest ->
                    (match c with
                     | Univ uu____11664 -> norm cfg (c :: env) stack_rest t1
                     | uu____11665 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____11670::[] ->
                              (log cfg
                                 (fun uu____11686  ->
                                    let uu____11687 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11687);
                               norm cfg (c :: env) stack_rest body)
                          | uu____11688::tl1 ->
                              (log cfg
                                 (fun uu____11707  ->
                                    let uu____11708 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11708);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___191_11738 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___191_11738.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____11799  ->
                          let uu____11800 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11800);
                     norm cfg env stack2 t1)
                | (Debug uu____11801)::uu____11802 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11809 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11809
                    else
                      (let uu____11811 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11811 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11835  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11851 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11851
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11861 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11861)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___192_11866 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___192_11866.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___192_11866.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11867 -> lopt in
                           (log cfg
                              (fun uu____11873  ->
                                 let uu____11874 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11874);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___193_11887 = cfg in
                               let uu____11888 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___193_11887.steps);
                                 tcenv = (uu___193_11887.tcenv);
                                 delta_level = (uu___193_11887.delta_level);
                                 primitive_steps = uu____11888
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____11897)::uu____11898 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11905 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11905
                    else
                      (let uu____11907 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11907 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11931  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11947 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11947
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11957 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11957)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___192_11962 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___192_11962.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___192_11962.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11963 -> lopt in
                           (log cfg
                              (fun uu____11969  ->
                                 let uu____11970 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11970);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___193_11983 = cfg in
                               let uu____11984 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___193_11983.steps);
                                 tcenv = (uu___193_11983.tcenv);
                                 delta_level = (uu___193_11983.delta_level);
                                 primitive_steps = uu____11984
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____11993)::uu____11994 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12005 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12005
                    else
                      (let uu____12007 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12007 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12031  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12047 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12047
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12057 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12057)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___192_12062 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___192_12062.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___192_12062.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12063 -> lopt in
                           (log cfg
                              (fun uu____12069  ->
                                 let uu____12070 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12070);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___193_12083 = cfg in
                               let uu____12084 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___193_12083.steps);
                                 tcenv = (uu___193_12083.tcenv);
                                 delta_level = (uu___193_12083.delta_level);
                                 primitive_steps = uu____12084
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____12093)::uu____12094 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12103 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12103
                    else
                      (let uu____12105 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12105 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12129  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12145 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12145
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12155 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12155)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___192_12160 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___192_12160.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___192_12160.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12161 -> lopt in
                           (log cfg
                              (fun uu____12167  ->
                                 let uu____12168 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12168);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___193_12181 = cfg in
                               let uu____12182 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___193_12181.steps);
                                 tcenv = (uu___193_12181.tcenv);
                                 delta_level = (uu___193_12181.delta_level);
                                 primitive_steps = uu____12182
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____12191)::uu____12192 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12207 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12207
                    else
                      (let uu____12209 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12209 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12233  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12249 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12249
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12259 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12259)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___192_12264 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___192_12264.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___192_12264.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12265 -> lopt in
                           (log cfg
                              (fun uu____12271  ->
                                 let uu____12272 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12272);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___193_12285 = cfg in
                               let uu____12286 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___193_12285.steps);
                                 tcenv = (uu___193_12285.tcenv);
                                 delta_level = (uu___193_12285.delta_level);
                                 primitive_steps = uu____12286
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12295 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12295
                    else
                      (let uu____12297 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12297 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12321  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12337 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12337
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12347 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12347)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___192_12352 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___192_12352.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___192_12352.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12353 -> lopt in
                           (log cfg
                              (fun uu____12359  ->
                                 let uu____12360 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12360);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___193_12373 = cfg in
                               let uu____12374 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___193_12373.steps);
                                 tcenv = (uu___193_12373.tcenv);
                                 delta_level = (uu___193_12373.delta_level);
                                 primitive_steps = uu____12374
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
                      (fun uu____12421  ->
                         fun stack2  ->
                           match uu____12421 with
                           | (a,aq) ->
                               let uu____12433 =
                                 let uu____12434 =
                                   let uu____12441 =
                                     let uu____12442 =
                                       let uu____12461 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____12461, false) in
                                     Clos uu____12442 in
                                   (uu____12441, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____12434 in
                               uu____12433 :: stack2) args) in
               (log cfg
                  (fun uu____12513  ->
                     let uu____12514 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12514);
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
                             ((let uu___194_12538 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___194_12538.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___194_12538.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____12539 ->
                      let uu____12544 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12544)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____12547 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____12547 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____12572 =
                          let uu____12573 =
                            let uu____12580 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___195_12582 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___195_12582.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___195_12582.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12580) in
                          FStar_Syntax_Syntax.Tm_refine uu____12573 in
                        mk uu____12572 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____12601 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____12601
               else
                 (let uu____12603 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____12603 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12611 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12623  -> Dummy :: env1) env) in
                        norm_comp cfg uu____12611 c1 in
                      let t2 =
                        let uu____12633 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____12633 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____12692)::uu____12693 -> norm cfg env stack1 t11
                | (Arg uu____12702)::uu____12703 -> norm cfg env stack1 t11
                | (App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____12712;
                       FStar_Syntax_Syntax.vars = uu____12713;_},uu____12714,uu____12715))::uu____12716
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____12723)::uu____12724 ->
                    norm cfg env stack1 t11
                | uu____12733 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____12737  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____12754 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____12754
                        | FStar_Util.Inr c ->
                            let uu____12762 = norm_comp cfg env c in
                            FStar_Util.Inr uu____12762 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____12768 =
                        let uu____12769 =
                          let uu____12770 =
                            let uu____12797 = FStar_Syntax_Util.unascribe t12 in
                            (uu____12797, (tc1, tacopt1), l) in
                          FStar_Syntax_Syntax.Tm_ascribed uu____12770 in
                        mk uu____12769 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____12768)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____12873,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____12874;
                               FStar_Syntax_Syntax.lbunivs = uu____12875;
                               FStar_Syntax_Syntax.lbtyp = uu____12876;
                               FStar_Syntax_Syntax.lbeff = uu____12877;
                               FStar_Syntax_Syntax.lbdef = uu____12878;_}::uu____12879),uu____12880)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____12916 =
                 (let uu____12919 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____12919) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____12921 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____12921))) in
               if uu____12916
               then
                 let env1 =
                   let uu____12925 =
                     let uu____12926 =
                       let uu____12945 =
                         FStar_Util.mk_ref FStar_Pervasives_Native.None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____12945,
                         false) in
                     Clos uu____12926 in
                   uu____12925 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____12997 =
                    let uu____13002 =
                      let uu____13003 =
                        let uu____13004 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____13004
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____13003] in
                    FStar_Syntax_Subst.open_term uu____13002 body in
                  match uu____12997 with
                  | (bs,body1) ->
                      let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                      let lbname =
                        let x =
                          let uu____13018 = FStar_List.hd bs in
                          FStar_Pervasives_Native.fst uu____13018 in
                        FStar_Util.Inl
                          (let uu___196_13028 = x in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___196_13028.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___196_13028.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = ty
                           }) in
                      let lb1 =
                        let uu___197_13030 = lb in
                        let uu____13031 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = lbname;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___197_13030.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = ty;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___197_13030.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____13031
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____13048  -> Dummy :: env1)
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
               let uu____13071 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____13071 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____13107 =
                               let uu___198_13108 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___198_13108.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___198_13108.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____13107 in
                           let uu____13109 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____13109 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____13129 =
                                   FStar_List.map (fun uu____13133  -> Dummy)
                                     lbs1 in
                                 let uu____13134 =
                                   let uu____13137 =
                                     FStar_List.map
                                       (fun uu____13145  -> Dummy) xs1 in
                                   FStar_List.append uu____13137 env in
                                 FStar_List.append uu____13129 uu____13134 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13157 =
                                       let uu___199_13158 = rc in
                                       let uu____13159 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___199_13158.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13159;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___199_13158.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____13157
                                 | uu____13166 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___200_13170 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___200_13170.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___200_13170.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____13174 =
                        FStar_List.map (fun uu____13178  -> Dummy) lbs2 in
                      FStar_List.append uu____13174 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____13180 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____13180 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___201_13196 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___201_13196.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___201_13196.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____13223 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____13223
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13242 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13293  ->
                        match uu____13293 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____13366 =
                                let uu___202_13367 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___202_13367.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___202_13367.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____13366 in
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
               (match uu____13242 with
                | (rec_env,memos,uu____13495) ->
                    let uu____13524 =
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
                             let uu____13929 =
                               let uu____13930 =
                                 let uu____13949 =
                                   FStar_Util.mk_ref
                                     FStar_Pervasives_Native.None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____13949, false) in
                               Clos uu____13930 in
                             uu____13929 :: env1)
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
                             FStar_Syntax_Syntax.pos = uu____14017;
                             FStar_Syntax_Syntax.vars = uu____14018;_},uu____14019,uu____14020))::uu____14021
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____14028 -> false in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____14038 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____14038
                        then
                          let uu___203_14039 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___203_14039.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps =
                              (uu___203_14039.primitive_steps)
                          }
                        else
                          (let uu___204_14041 = cfg in
                           {
                             steps =
                               (FStar_List.append [Exclude Zeta] cfg.steps);
                             tcenv = (uu___204_14041.tcenv);
                             delta_level = (uu___204_14041.delta_level);
                             primitive_steps =
                               (uu___204_14041.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____14043 =
                         let uu____14044 = FStar_Syntax_Subst.compress head1 in
                         uu____14044.FStar_Syntax_Syntax.n in
                       match uu____14043 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____14062 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____14062 with
                            | (uu____14063,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____14069 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____14077 =
                                         let uu____14078 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____14078.FStar_Syntax_Syntax.n in
                                       match uu____14077 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____14084,uu____14085))
                                           ->
                                           let uu____14094 =
                                             let uu____14095 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____14095.FStar_Syntax_Syntax.n in
                                           (match uu____14094 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____14101,msrc,uu____14103))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____14112 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14112
                                            | uu____14113 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____14114 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____14115 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____14115 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___205_14120 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___205_14120.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___205_14120.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___205_14120.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____14121 =
                                            FStar_List.tl stack1 in
                                          let uu____14122 =
                                            let uu____14123 =
                                              let uu____14126 =
                                                let uu____14127 =
                                                  let uu____14140 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____14140) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____14127 in
                                              FStar_Syntax_Syntax.mk
                                                uu____14126 in
                                            uu____14123
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____14121
                                            uu____14122
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____14156 =
                                            let uu____14157 = is_return body in
                                            match uu____14157 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____14161;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____14162;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____14167 -> false in
                                          if uu____14156
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
                                               let uu____14191 =
                                                 let uu____14194 =
                                                   let uu____14195 =
                                                     let uu____14212 =
                                                       let uu____14215 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____14215] in
                                                     (uu____14212, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc)) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____14195 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____14194 in
                                               uu____14191
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____14231 =
                                                 let uu____14232 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____14232.FStar_Syntax_Syntax.n in
                                               match uu____14231 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____14238::uu____14239::[])
                                                   ->
                                                   let uu____14246 =
                                                     let uu____14249 =
                                                       let uu____14250 =
                                                         let uu____14257 =
                                                           let uu____14260 =
                                                             let uu____14261
                                                               =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____14261 in
                                                           let uu____14262 =
                                                             let uu____14265
                                                               =
                                                               let uu____14266
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____14266 in
                                                             [uu____14265] in
                                                           uu____14260 ::
                                                             uu____14262 in
                                                         (bind1, uu____14257) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____14250 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____14249 in
                                                   uu____14246
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____14274 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____14280 =
                                                 let uu____14283 =
                                                   let uu____14284 =
                                                     let uu____14299 =
                                                       let uu____14302 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____14303 =
                                                         let uu____14306 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____14307 =
                                                           let uu____14310 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____14311 =
                                                             let uu____14314
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____14315
                                                               =
                                                               let uu____14318
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____14319
                                                                 =
                                                                 let uu____14322
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____14322] in
                                                               uu____14318 ::
                                                                 uu____14319 in
                                                             uu____14314 ::
                                                               uu____14315 in
                                                           uu____14310 ::
                                                             uu____14311 in
                                                         uu____14306 ::
                                                           uu____14307 in
                                                       uu____14302 ::
                                                         uu____14303 in
                                                     (bind_inst, uu____14299) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____14284 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____14283 in
                                               uu____14280
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____14330 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____14330 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____14354 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____14354 with
                            | (uu____14355,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____14384 =
                                        let uu____14385 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____14385.FStar_Syntax_Syntax.n in
                                      match uu____14384 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____14391) -> t4
                                      | uu____14396 -> head2 in
                                    let uu____14397 =
                                      let uu____14398 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____14398.FStar_Syntax_Syntax.n in
                                    match uu____14397 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____14404 ->
                                        FStar_Pervasives_Native.None in
                                  let uu____14405 = maybe_extract_fv head2 in
                                  match uu____14405 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____14415 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____14415
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____14420 =
                                          maybe_extract_fv head3 in
                                        match uu____14420 with
                                        | FStar_Pervasives_Native.Some
                                            uu____14425 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____14426 ->
                                            FStar_Pervasives_Native.Some
                                              false in
                                      (head3, action_unfolded)
                                  | uu____14431 ->
                                      (head2, FStar_Pervasives_Native.None) in
                                ((let is_arg_impure uu____14446 =
                                    match uu____14446 with
                                    | (e,q) ->
                                        let uu____14453 =
                                          let uu____14454 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____14454.FStar_Syntax_Syntax.n in
                                        (match uu____14453 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____14469 -> false) in
                                  let uu____14470 =
                                    let uu____14471 =
                                      let uu____14478 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____14478 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____14471 in
                                  if uu____14470
                                  then
                                    let uu____14483 =
                                      let uu____14484 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____14484 in
                                    failwith uu____14483
                                  else ());
                                 (let uu____14486 =
                                    maybe_unfold_action head_app in
                                  match uu____14486 with
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
                                      let uu____14525 = FStar_List.tl stack1 in
                                      norm cfg env uu____14525 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____14539 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____14539 in
                           let uu____14540 = FStar_List.tl stack1 in
                           norm cfg env uu____14540 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____14661  ->
                                     match uu____14661 with
                                     | (pat,wopt,tm) ->
                                         let uu____14709 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____14709))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____14741 = FStar_List.tl stack1 in
                           norm cfg env uu____14741 tm
                       | uu____14742 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.pos = uu____14751;
                             FStar_Syntax_Syntax.vars = uu____14752;_},uu____14753,uu____14754))::uu____14755
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____14762 -> false in
                    if should_reify
                    then
                      let uu____14763 = FStar_List.tl stack1 in
                      let uu____14764 =
                        let uu____14765 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____14765 in
                      norm cfg env uu____14763 uu____14764
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____14768 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____14768
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___206_14777 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___206_14777.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___206_14777.primitive_steps)
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
                | uu____14779 ->
                    if FStar_List.contains Unmeta cfg.steps
                    then norm cfg env stack1 head1
                    else
                      (match stack1 with
                       | uu____14781::uu____14782 ->
                           (match m with
                            | FStar_Syntax_Syntax.Meta_labeled
                                (l,r,uu____14787) ->
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
                            | uu____14812 -> norm cfg env stack1 head1)
                       | [] ->
                           let head2 = norm cfg env [] head1 in
                           let m1 =
                             match m with
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let uu____14826 =
                                   norm_pattern_args cfg env args in
                                 FStar_Syntax_Syntax.Meta_pattern uu____14826
                             | uu____14837 -> m in
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
              let uu____14849 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____14849 with
              | (uu____14850,return_repr) ->
                  let return_inst =
                    let uu____14859 =
                      let uu____14860 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____14860.FStar_Syntax_Syntax.n in
                    match uu____14859 with
                    | FStar_Syntax_Syntax.Tm_uinst
                        (return_tm,uu____14866::[]) ->
                        let uu____14873 =
                          let uu____14876 =
                            let uu____14877 =
                              let uu____14884 =
                                let uu____14887 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____14887] in
                              (return_tm, uu____14884) in
                            FStar_Syntax_Syntax.Tm_uinst uu____14877 in
                          FStar_Syntax_Syntax.mk uu____14876 in
                        uu____14873 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____14895 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____14898 =
                    let uu____14901 =
                      let uu____14902 =
                        let uu____14917 =
                          let uu____14920 = FStar_Syntax_Syntax.as_arg t in
                          let uu____14921 =
                            let uu____14924 = FStar_Syntax_Syntax.as_arg e in
                            [uu____14924] in
                          uu____14920 :: uu____14921 in
                        (return_inst, uu____14917) in
                      FStar_Syntax_Syntax.Tm_app uu____14902 in
                    FStar_Syntax_Syntax.mk uu____14901 in
                  uu____14898 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____14933 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____14933 with
               | FStar_Pervasives_Native.None  ->
                   let uu____14936 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____14936
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____14937;
                     FStar_TypeChecker_Env.mtarget = uu____14938;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____14939;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____14950;
                     FStar_TypeChecker_Env.mtarget = uu____14951;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____14952;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____14970 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____14970)
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
                (fun uu____15026  ->
                   match uu____15026 with
                   | (a,imp) ->
                       let uu____15037 = norm cfg env [] a in
                       (uu____15037, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___207_15054 = comp1 in
            let uu____15057 =
              let uu____15058 =
                let uu____15067 = norm cfg env [] t in
                let uu____15068 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____15067, uu____15068) in
              FStar_Syntax_Syntax.Total uu____15058 in
            {
              FStar_Syntax_Syntax.n = uu____15057;
              FStar_Syntax_Syntax.pos =
                (uu___207_15054.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___207_15054.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___208_15083 = comp1 in
            let uu____15086 =
              let uu____15087 =
                let uu____15096 = norm cfg env [] t in
                let uu____15097 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____15096, uu____15097) in
              FStar_Syntax_Syntax.GTotal uu____15087 in
            {
              FStar_Syntax_Syntax.n = uu____15086;
              FStar_Syntax_Syntax.pos =
                (uu___208_15083.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___208_15083.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____15149  ->
                      match uu____15149 with
                      | (a,i) ->
                          let uu____15160 = norm cfg env [] a in
                          (uu____15160, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___161_15171  ->
                      match uu___161_15171 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____15175 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____15175
                      | f -> f)) in
            let uu___209_15179 = comp1 in
            let uu____15182 =
              let uu____15183 =
                let uu___210_15184 = ct in
                let uu____15185 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____15186 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____15189 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____15185;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___210_15184.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____15186;
                  FStar_Syntax_Syntax.effect_args = uu____15189;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____15183 in
            {
              FStar_Syntax_Syntax.n = uu____15182;
              FStar_Syntax_Syntax.pos =
                (uu___209_15179.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___209_15179.FStar_Syntax_Syntax.vars)
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
            (let uu___211_15207 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___211_15207.tcenv);
               delta_level = (uu___211_15207.delta_level);
               primitive_steps = (uu___211_15207.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____15212 = norm1 t in
          FStar_Syntax_Util.non_informative uu____15212 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____15215 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___212_15234 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.pos =
                (uu___212_15234.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___212_15234.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____15241 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____15241
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
                    let uu___213_15252 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___213_15252.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___213_15252.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___213_15252.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___214_15254 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___214_15254.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___214_15254.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___214_15254.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___214_15254.FStar_Syntax_Syntax.flags)
                    } in
              let uu___215_15255 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos =
                  (uu___215_15255.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___215_15255.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____15257 -> c
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____15260  ->
        match uu____15260 with
        | (x,imp) ->
            let uu____15263 =
              let uu___216_15264 = x in
              let uu____15265 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___216_15264.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___216_15264.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____15265
              } in
            (uu____15263, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____15271 =
          FStar_List.fold_left
            (fun uu____15289  ->
               fun b  ->
                 match uu____15289 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____15271 with | (nbs,uu____15317) -> FStar_List.rev nbs
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
            let uu____15333 =
              let uu___217_15334 = rc in
              let uu____15335 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___217_15334.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____15335;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___217_15334.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____15333
        | uu____15342 -> lopt
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
              ((let uu____15355 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____15355
                then
                  let time_now = FStar_Util.now () in
                  let uu____15357 =
                    let uu____15358 =
                      let uu____15359 =
                        FStar_Util.time_diff time_then time_now in
                      FStar_Pervasives_Native.snd uu____15359 in
                    FStar_Util.string_of_int uu____15358 in
                  let uu____15364 = FStar_Syntax_Print.term_to_string tm in
                  let uu____15365 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                    uu____15357 uu____15364 uu____15365
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___218_15383 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___218_15383.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____15452  ->
                    let uu____15453 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____15453);
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
              let uu____15489 =
                let uu___219_15490 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___219_15490.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___219_15490.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____15489
          | (Arg (Univ uu____15491,uu____15492,uu____15493))::uu____15494 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____15497,uu____15498))::uu____15499 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____15515),aq,r))::stack2 ->
              (log cfg
                 (fun uu____15544  ->
                    let uu____15545 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____15545);
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
                 (let uu____15555 = FStar_ST.op_Bang m in
                  match uu____15555 with
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
                  | FStar_Pervasives_Native.Some (uu____15655,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq)
                          FStar_Pervasives_Native.None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 =
                FStar_Syntax_Syntax.extend_app head1 (t, aq)
                  FStar_Pervasives_Native.None r in
              let uu____15679 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____15679
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____15689  ->
                    let uu____15690 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____15690);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____15695 =
                  log cfg
                    (fun uu____15700  ->
                       let uu____15701 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____15702 =
                         let uu____15703 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____15720  ->
                                   match uu____15720 with
                                   | (p,uu____15730,uu____15731) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____15703
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____15701 uu____15702);
                  (let whnf1 = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___162_15748  ->
                               match uu___162_15748 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____15749 -> false)) in
                     let steps' =
                       let uu____15753 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____15753
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___220_15757 = cfg in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___220_15757.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___220_15757.primitive_steps)
                     } in
                   let norm_or_whnf env2 t1 =
                     if whnf1
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____15801 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____15824 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____15890  ->
                                   fun uu____15891  ->
                                     match (uu____15890, uu____15891) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____15994 = norm_pat env3 p1 in
                                         (match uu____15994 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____15824 with
                          | (pats1,env3) ->
                              ((let uu___221_16096 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.p =
                                    (uu___221_16096.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___222_16115 = x in
                           let uu____16116 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___222_16115.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___222_16115.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16116
                           } in
                         ((let uu___223_16124 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.p =
                               (uu___223_16124.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___224_16129 = x in
                           let uu____16130 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___224_16129.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___224_16129.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16130
                           } in
                         ((let uu___225_16138 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.p =
                               (uu___225_16138.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___226_16148 = x in
                           let uu____16149 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___226_16148.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___226_16148.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16149
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___227_16158 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.p =
                               (uu___227_16158.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf1 -> branches
                     | uu____16162 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____16176 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____16176 with
                                 | (p,wopt,e) ->
                                     let uu____16196 = norm_pat env1 p in
                                     (match uu____16196 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Pervasives_Native.Some w
                                                ->
                                                let uu____16227 =
                                                  norm_or_whnf env2 w in
                                                FStar_Pervasives_Native.Some
                                                  uu____16227 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____16233 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____16233) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____16243) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____16248 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____16249;
                        FStar_Syntax_Syntax.fv_delta = uu____16250;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Data_ctor );_}
                      -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____16251;
                        FStar_Syntax_Syntax.fv_delta = uu____16252;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Record_ctor uu____16253);_}
                      -> true
                  | uu____16260 -> false in
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
                  let uu____16389 =
                    FStar_Syntax_Util.head_and_args scrutinee1 in
                  match uu____16389 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var uu____16438 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_wild uu____16441 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____16444 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee1.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____16463 ->
                                let uu____16464 =
                                  let uu____16465 = is_cons head1 in
                                  Prims.op_Negation uu____16465 in
                                FStar_Util.Inr uu____16464)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____16486 =
                             let uu____16487 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____16487.FStar_Syntax_Syntax.n in
                           (match uu____16486 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____16497 ->
                                let uu____16498 =
                                  let uu____16499 = is_cons head1 in
                                  Prims.op_Negation uu____16499 in
                                FStar_Util.Inr uu____16498))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____16552)::rest_a,(p1,uu____16555)::rest_p) ->
                      let uu____16599 = matches_pat t1 p1 in
                      (match uu____16599 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____16624 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____16726 = matches_pat scrutinee1 p1 in
                      (match uu____16726 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____16746  ->
                                 let uu____16747 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____16748 =
                                   let uu____16749 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____16749
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____16747 uu____16748);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____16766 =
                                        let uu____16767 =
                                          let uu____16786 =
                                            FStar_Util.mk_ref
                                              (FStar_Pervasives_Native.Some
                                                 ([], t1)) in
                                          ([], t1, uu____16786, false) in
                                        Clos uu____16767 in
                                      uu____16766 :: env2) env1 s in
                             let uu____16839 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____16839))) in
                let uu____16840 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____16840
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___163_16863  ->
                match uu___163_16863 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____16867 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____16873 -> d in
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
            let uu___228_16902 = config s e in
            {
              steps = (uu___228_16902.steps);
              tcenv = (uu___228_16902.tcenv);
              delta_level = (uu___228_16902.delta_level);
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
      fun t  -> let uu____16927 = config s e in norm_comp uu____16927 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____16936 = config [] env in norm_universe uu____16936 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let uu____16945 = config [] env in ghost_to_pure_aux uu____16945 [] c
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
        let uu____16959 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____16959 in
      let uu____16960 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____16960
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___229_16962 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___229_16962.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___229_16962.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____16965  ->
                    let uu____16966 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____16966))
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
            ((let uu____16985 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____16985);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____16998 = config [AllowUnboundUniverses] env in
          norm_comp uu____16998 [] c
        with
        | e ->
            ((let uu____17005 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____17005);
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
                   let uu____17045 =
                     let uu____17046 =
                       let uu____17053 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____17053) in
                     FStar_Syntax_Syntax.Tm_refine uu____17046 in
                   mk uu____17045 t01.FStar_Syntax_Syntax.pos
               | uu____17058 -> t2)
          | uu____17059 -> t2 in
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
        let uu____17111 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____17111 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____17140 ->
                 let uu____17147 = FStar_Syntax_Util.abs_formals e in
                 (match uu____17147 with
                  | (actuals,uu____17157,uu____17158) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____17172 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____17172 with
                         | (binders,args) ->
                             let uu____17189 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____17189
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
      | uu____17199 ->
          let uu____17200 = FStar_Syntax_Util.head_and_args t in
          (match uu____17200 with
           | (head1,args) ->
               let uu____17237 =
                 let uu____17238 = FStar_Syntax_Subst.compress head1 in
                 uu____17238.FStar_Syntax_Syntax.n in
               (match uu____17237 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____17241,thead) ->
                    let uu____17267 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____17267 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____17309 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___234_17317 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___234_17317.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___234_17317.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___234_17317.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___234_17317.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___234_17317.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___234_17317.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___234_17317.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___234_17317.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___234_17317.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___234_17317.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___234_17317.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___234_17317.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___234_17317.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___234_17317.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___234_17317.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___234_17317.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___234_17317.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___234_17317.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___234_17317.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___234_17317.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___234_17317.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___234_17317.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___234_17317.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___234_17317.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___234_17317.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___234_17317.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___234_17317.FStar_TypeChecker_Env.identifier_info)
                                 }) t in
                            match uu____17309 with
                            | (uu____17318,ty,uu____17320) ->
                                eta_expand_with_type env t ty))
                | uu____17321 ->
                    let uu____17322 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___235_17330 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___235_17330.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___235_17330.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___235_17330.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___235_17330.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___235_17330.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___235_17330.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___235_17330.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___235_17330.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___235_17330.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___235_17330.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___235_17330.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___235_17330.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___235_17330.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___235_17330.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___235_17330.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___235_17330.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___235_17330.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___235_17330.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___235_17330.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___235_17330.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.type_of =
                             (uu___235_17330.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___235_17330.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___235_17330.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___235_17330.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___235_17330.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___235_17330.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___235_17330.FStar_TypeChecker_Env.identifier_info)
                         }) t in
                    (match uu____17322 with
                     | (uu____17331,ty,uu____17333) ->
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
            | (uu____17411,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____17417,FStar_Util.Inl t) ->
                let uu____17423 =
                  let uu____17426 =
                    let uu____17427 =
                      let uu____17440 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____17440) in
                    FStar_Syntax_Syntax.Tm_arrow uu____17427 in
                  FStar_Syntax_Syntax.mk uu____17426 in
                uu____17423 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____17444 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____17444 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____17471 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____17526 ->
                    let uu____17527 =
                      let uu____17536 =
                        let uu____17537 = FStar_Syntax_Subst.compress t3 in
                        uu____17537.FStar_Syntax_Syntax.n in
                      (uu____17536, tc) in
                    (match uu____17527 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____17562) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____17599) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____17638,FStar_Util.Inl uu____17639) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____17662 -> failwith "Impossible") in
              (match uu____17471 with
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
          let uu____17771 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____17771 with
          | (univ_names1,binders1,tc) ->
              let uu____17829 = FStar_Util.left tc in
              (univ_names1, binders1, uu____17829)
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
          let uu____17868 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____17868 with
          | (univ_names1,binders1,tc) ->
              let uu____17928 = FStar_Util.right tc in
              (univ_names1, binders1, uu____17928)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____17963 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____17963 with
           | (univ_names1,binders1,typ1) ->
               let uu___236_17991 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___236_17991.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___236_17991.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___236_17991.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___236_17991.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___237_18012 = s in
          let uu____18013 =
            let uu____18014 =
              let uu____18023 = FStar_List.map (elim_uvars env) sigs in
              (uu____18023, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____18014 in
          {
            FStar_Syntax_Syntax.sigel = uu____18013;
            FStar_Syntax_Syntax.sigrng =
              (uu___237_18012.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___237_18012.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___237_18012.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___237_18012.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____18040 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____18040 with
           | (univ_names1,uu____18058,typ1) ->
               let uu___238_18072 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___238_18072.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___238_18072.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___238_18072.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___238_18072.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____18078 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____18078 with
           | (univ_names1,uu____18096,typ1) ->
               let uu___239_18110 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___239_18110.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___239_18110.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___239_18110.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___239_18110.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____18144 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____18144 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____18167 =
                            let uu____18168 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____18168 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____18167 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___240_18171 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___240_18171.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___240_18171.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___241_18172 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___241_18172.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___241_18172.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___241_18172.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___241_18172.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___242_18184 = s in
          let uu____18185 =
            let uu____18186 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____18186 in
          {
            FStar_Syntax_Syntax.sigel = uu____18185;
            FStar_Syntax_Syntax.sigrng =
              (uu___242_18184.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___242_18184.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___242_18184.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___242_18184.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____18190 = elim_uvars_aux_t env us [] t in
          (match uu____18190 with
           | (us1,uu____18208,t1) ->
               let uu___243_18222 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___243_18222.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___243_18222.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___243_18222.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___243_18222.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____18223 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____18225 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____18225 with
           | (univs1,binders,signature) ->
               let uu____18253 =
                 let uu____18262 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____18262 with
                 | (univs_opening,univs2) ->
                     let uu____18289 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____18289) in
               (match uu____18253 with
                | (univs_opening,univs_closing) ->
                    let uu____18306 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____18312 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____18313 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____18312, uu____18313) in
                    (match uu____18306 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____18335 =
                           match uu____18335 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____18353 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____18353 with
                                | (us1,t1) ->
                                    let uu____18364 =
                                      let uu____18369 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____18376 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____18369, uu____18376) in
                                    (match uu____18364 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____18389 =
                                           let uu____18394 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____18403 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____18394, uu____18403) in
                                         (match uu____18389 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____18419 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____18419 in
                                              let uu____18420 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____18420 with
                                               | (uu____18441,uu____18442,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____18457 =
                                                       let uu____18458 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____18458 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____18457 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____18463 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____18463 with
                           | (uu____18476,uu____18477,t1) -> t1 in
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
                             | uu____18537 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____18554 =
                               let uu____18555 =
                                 FStar_Syntax_Subst.compress body in
                               uu____18555.FStar_Syntax_Syntax.n in
                             match uu____18554 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____18614 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____18643 =
                               let uu____18644 =
                                 FStar_Syntax_Subst.compress t in
                               uu____18644.FStar_Syntax_Syntax.n in
                             match uu____18643 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____18665) ->
                                 let uu____18686 = destruct_action_body body in
                                 (match uu____18686 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____18731 ->
                                 let uu____18732 = destruct_action_body t in
                                 (match uu____18732 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____18781 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____18781 with
                           | (action_univs,t) ->
                               let uu____18790 = destruct_action_typ_templ t in
                               (match uu____18790 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___244_18831 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___244_18831.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___244_18831.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___245_18833 = ed in
                           let uu____18834 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____18835 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____18836 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____18837 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____18838 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____18839 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____18840 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____18841 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____18842 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____18843 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____18844 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____18845 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____18846 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____18847 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___245_18833.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___245_18833.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____18834;
                             FStar_Syntax_Syntax.bind_wp = uu____18835;
                             FStar_Syntax_Syntax.if_then_else = uu____18836;
                             FStar_Syntax_Syntax.ite_wp = uu____18837;
                             FStar_Syntax_Syntax.stronger = uu____18838;
                             FStar_Syntax_Syntax.close_wp = uu____18839;
                             FStar_Syntax_Syntax.assert_p = uu____18840;
                             FStar_Syntax_Syntax.assume_p = uu____18841;
                             FStar_Syntax_Syntax.null_wp = uu____18842;
                             FStar_Syntax_Syntax.trivial = uu____18843;
                             FStar_Syntax_Syntax.repr = uu____18844;
                             FStar_Syntax_Syntax.return_repr = uu____18845;
                             FStar_Syntax_Syntax.bind_repr = uu____18846;
                             FStar_Syntax_Syntax.actions = uu____18847
                           } in
                         let uu___246_18850 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___246_18850.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___246_18850.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___246_18850.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___246_18850.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___164_18867 =
            match uu___164_18867 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____18894 = elim_uvars_aux_t env us [] t in
                (match uu____18894 with
                 | (us1,uu____18918,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___247_18937 = sub_eff in
            let uu____18938 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____18941 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___247_18937.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___247_18937.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____18938;
              FStar_Syntax_Syntax.lift = uu____18941
            } in
          let uu___248_18944 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___248_18944.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___248_18944.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___248_18944.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___248_18944.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____18954 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____18954 with
           | (univ_names1,binders1,comp1) ->
               let uu___249_18988 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___249_18988.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___249_18988.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___249_18988.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___249_18988.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____18999 -> s