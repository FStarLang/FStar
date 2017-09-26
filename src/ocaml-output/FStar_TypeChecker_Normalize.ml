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
    | uu____5272::(t,uu____5274)::({
                                     FStar_Syntax_Syntax.n =
                                       FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_range r1);
                                     FStar_Syntax_Syntax.pos = uu____5276;
                                     FStar_Syntax_Syntax.vars = uu____5277;_},uu____5278)::[]
        ->
        FStar_Pervasives_Native.Some
          (let uu___183_5320 = t in
           {
             FStar_Syntax_Syntax.n = (uu___183_5320.FStar_Syntax_Syntax.n);
             FStar_Syntax_Syntax.pos = r1;
             FStar_Syntax_Syntax.vars =
               (uu___183_5320.FStar_Syntax_Syntax.vars)
           })
    | uu____5323 -> FStar_Pervasives_Native.None in
  let mk_range1 r args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____5404 =
          let uu____5425 = arg_as_string fn in
          let uu____5428 = arg_as_int from_line in
          let uu____5431 = arg_as_int from_col in
          let uu____5434 = arg_as_int to_line in
          let uu____5437 = arg_as_int to_col in
          (uu____5425, uu____5428, uu____5431, uu____5434, uu____5437) in
        (match uu____5404 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r1 =
               let uu____5468 = FStar_Range.mk_pos from_l from_c in
               let uu____5469 = FStar_Range.mk_pos to_l to_c in
               FStar_Range.mk_range fn1 uu____5468 uu____5469 in
             let uu____5470 = term_of_range r1 in
             FStar_Pervasives_Native.Some uu____5470
         | uu____5475 -> FStar_Pervasives_Native.None)
    | uu____5496 -> FStar_Pervasives_Native.None in
  let decidable_eq neg rng args =
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) rng in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) rng in
    match args with
    | (_typ,uu____5526)::(a1,uu____5528)::(a2,uu____5530)::[] ->
        let uu____5567 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____5567 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____5580 -> FStar_Pervasives_Native.None)
    | uu____5581 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____5599 =
      let uu____5614 =
        let uu____5629 =
          let uu____5644 =
            let uu____5659 =
              let uu____5674 =
                let uu____5689 =
                  let uu____5704 =
                    let uu____5719 =
                      let uu____5734 =
                        let uu____5749 =
                          let uu____5764 =
                            let uu____5779 =
                              let uu____5794 =
                                let uu____5809 =
                                  let uu____5824 =
                                    let uu____5839 =
                                      let uu____5854 =
                                        let uu____5869 =
                                          let uu____5884 =
                                            let uu____5899 =
                                              let uu____5912 =
                                                FStar_Parser_Const.p2l
                                                  ["FStar";
                                                  "String";
                                                  "list_of_string"] in
                                              (uu____5912,
                                                (Prims.parse_int "1"),
                                                (unary_op arg_as_string
                                                   list_of_string')) in
                                            let uu____5919 =
                                              let uu____5934 =
                                                let uu____5947 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "string_of_list"] in
                                                (uu____5947,
                                                  (Prims.parse_int "1"),
                                                  (unary_op
                                                     (arg_as_list arg_as_char)
                                                     string_of_list')) in
                                              let uu____5956 =
                                                let uu____5971 =
                                                  let uu____5990 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "concat"] in
                                                  (uu____5990,
                                                    (Prims.parse_int "2"),
                                                    string_concat') in
                                                let uu____6003 =
                                                  let uu____6024 =
                                                    let uu____6045 =
                                                      FStar_Parser_Const.p2l
                                                        ["Prims"; "range_of"] in
                                                    (uu____6045,
                                                      (Prims.parse_int "2"),
                                                      range_of1) in
                                                  let uu____6060 =
                                                    let uu____6083 =
                                                      let uu____6104 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "set_range_of"] in
                                                      (uu____6104,
                                                        (Prims.parse_int "3"),
                                                        set_range_of1) in
                                                    let uu____6119 =
                                                      let uu____6142 =
                                                        let uu____6161 =
                                                          FStar_Parser_Const.p2l
                                                            ["Prims";
                                                            "mk_range"] in
                                                        (uu____6161,
                                                          (Prims.parse_int
                                                             "5"), mk_range1) in
                                                      [uu____6142] in
                                                    uu____6083 :: uu____6119 in
                                                  uu____6024 :: uu____6060 in
                                                uu____5971 :: uu____6003 in
                                              uu____5934 :: uu____5956 in
                                            uu____5899 :: uu____5919 in
                                          (FStar_Parser_Const.op_notEq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq true)) ::
                                            uu____5884 in
                                        (FStar_Parser_Const.op_Eq,
                                          (Prims.parse_int "3"),
                                          (decidable_eq false)) :: uu____5869 in
                                      (FStar_Parser_Const.string_compare,
                                        (Prims.parse_int "2"),
                                        (binary_op arg_as_string
                                           string_compare'))
                                        :: uu____5854 in
                                    (FStar_Parser_Const.string_of_bool_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_bool string_of_bool2))
                                      :: uu____5839 in
                                  (FStar_Parser_Const.string_of_int_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_int string_of_int2)) ::
                                    uu____5824 in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____5809 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5794 in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____5779 in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____5764 in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____5749 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____5734 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
                      :: uu____5719 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____5704 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____5689 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____5674 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____5659 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____5644 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____5629 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____5614 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____5599 in
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
      let uu____6768 =
        let uu____6769 =
          let uu____6770 = FStar_Syntax_Syntax.as_arg c in [uu____6770] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6769 in
      uu____6768 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____6805 =
              let uu____6818 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____6818, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____6837  ->
                        fun uu____6838  ->
                          match (uu____6837, uu____6838) with
                          | ((int_to_t1,x),(uu____6857,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____6867 =
              let uu____6882 =
                let uu____6895 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____6895, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____6914  ->
                          fun uu____6915  ->
                            match (uu____6914, uu____6915) with
                            | ((int_to_t1,x),(uu____6934,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____6944 =
                let uu____6959 =
                  let uu____6972 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____6972, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____6991  ->
                            fun uu____6992  ->
                              match (uu____6991, uu____6992) with
                              | ((int_to_t1,x),(uu____7011,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____6959] in
              uu____6882 :: uu____6944 in
            uu____6805 :: uu____6867)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop r args =
    match args with
    | (_typ,uu____7107)::(a1,uu____7109)::(a2,uu____7111)::[] ->
        let uu____7148 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____7148 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___184_7154 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___184_7154.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___184_7154.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___185_7158 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___185_7158.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___185_7158.FStar_Syntax_Syntax.vars)
                })
         | uu____7159 -> FStar_Pervasives_Native.None)
    | (_typ,uu____7161)::uu____7162::(a1,uu____7164)::(a2,uu____7166)::[] ->
        let uu____7215 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____7215 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___184_7221 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___184_7221.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___184_7221.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___185_7225 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___185_7225.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___185_7225.FStar_Syntax_Syntax.vars)
                })
         | uu____7226 -> FStar_Pervasives_Native.None)
    | uu____7227 -> failwith "Unexpected number of arguments" in
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
      let uu____7240 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops cfg.steps) in
      if uu____7240
      then tm
      else
        (let uu____7242 = FStar_Syntax_Util.head_and_args tm in
         match uu____7242 with
         | (head1,args) ->
             let uu____7279 =
               let uu____7280 = FStar_Syntax_Util.un_uinst head1 in
               uu____7280.FStar_Syntax_Syntax.n in
             (match uu____7279 with
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____7284 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps in
                  (match uu____7284 with
                   | FStar_Pervasives_Native.None  -> tm
                   | FStar_Pervasives_Native.Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then tm
                       else
                         (let uu____7297 =
                            prim_step.interpretation
                              head1.FStar_Syntax_Syntax.pos args in
                          match uu____7297 with
                          | FStar_Pervasives_Native.None  -> tm
                          | FStar_Pervasives_Native.Some reduced -> reduced))
              | uu____7301 -> tm))
let reduce_equality:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___186_7312 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___186_7312.tcenv);
           delta_level = (uu___186_7312.delta_level);
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
        let uu___187_7336 = t in
        {
          FStar_Syntax_Syntax.n = (uu___187_7336.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___187_7336.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid ->
            FStar_Pervasives_Native.Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid ->
            FStar_Pervasives_Native.Some false
        | uu____7353 -> FStar_Pervasives_Native.None in
      let simplify1 arg = ((simp_t (FStar_Pervasives_Native.fst arg)), arg) in
      let tm1 = reduce_primops cfg tm in
      let uu____7393 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps) in
      if uu____7393
      then tm1
      else
        (match tm1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.pos = uu____7396;
                     FStar_Syntax_Syntax.vars = uu____7397;_},uu____7398);
                FStar_Syntax_Syntax.pos = uu____7399;
                FStar_Syntax_Syntax.vars = uu____7400;_},args)
             ->
             let uu____7426 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
             if uu____7426
             then
               let uu____7427 =
                 FStar_All.pipe_right args (FStar_List.map simplify1) in
               (match uu____7427 with
                | (FStar_Pervasives_Native.Some (true ),uu____7482)::
                    (uu____7483,(arg,uu____7485))::[] -> arg
                | (uu____7550,(arg,uu____7552))::(FStar_Pervasives_Native.Some
                                                  (true ),uu____7553)::[]
                    -> arg
                | (FStar_Pervasives_Native.Some (false ),uu____7618)::uu____7619::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____7682::(FStar_Pervasives_Native.Some (false
                               ),uu____7683)::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____7746 -> tm1)
             else
               (let uu____7762 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
                if uu____7762
                then
                  let uu____7763 =
                    FStar_All.pipe_right args (FStar_List.map simplify1) in
                  match uu____7763 with
                  | (FStar_Pervasives_Native.Some (true ),uu____7818)::uu____7819::[]
                      -> w FStar_Syntax_Util.t_true
                  | uu____7882::(FStar_Pervasives_Native.Some (true
                                 ),uu____7883)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____7946)::
                      (uu____7947,(arg,uu____7949))::[] -> arg
                  | (uu____8014,(arg,uu____8016))::(FStar_Pervasives_Native.Some
                                                    (false ),uu____8017)::[]
                      -> arg
                  | uu____8082 -> tm1
                else
                  (let uu____8098 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.imp_lid in
                   if uu____8098
                   then
                     let uu____8099 =
                       FStar_All.pipe_right args (FStar_List.map simplify1) in
                     match uu____8099 with
                     | uu____8154::(FStar_Pervasives_Native.Some (true
                                    ),uu____8155)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____8218)::uu____8219::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____8282)::
                         (uu____8283,(arg,uu____8285))::[] -> arg
                     | (uu____8350,(p,uu____8352))::(uu____8353,(q,uu____8355))::[]
                         ->
                         let uu____8420 = FStar_Syntax_Util.term_eq p q in
                         (if uu____8420
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____8422 -> tm1
                   else
                     (let uu____8438 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____8438
                      then
                        let uu____8439 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1) in
                        match uu____8439 with
                        | (FStar_Pervasives_Native.Some (true ),uu____8494)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____8533)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____8572 -> tm1
                      else
                        (let uu____8588 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____8588
                         then
                           match args with
                           | (t,uu____8590)::[] ->
                               let uu____8607 =
                                 let uu____8608 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____8608.FStar_Syntax_Syntax.n in
                               (match uu____8607 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____8611::[],body,uu____8613) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____8640 -> tm1)
                                | uu____8643 -> tm1)
                           | (uu____8644,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____8645))::
                               (t,uu____8647)::[] ->
                               let uu____8686 =
                                 let uu____8687 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____8687.FStar_Syntax_Syntax.n in
                               (match uu____8686 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____8690::[],body,uu____8692) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____8719 -> tm1)
                                | uu____8722 -> tm1)
                           | uu____8723 -> tm1
                         else
                           (let uu____8733 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____8733
                            then
                              match args with
                              | (t,uu____8735)::[] ->
                                  let uu____8752 =
                                    let uu____8753 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____8753.FStar_Syntax_Syntax.n in
                                  (match uu____8752 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____8756::[],body,uu____8758) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____8785 -> tm1)
                                   | uu____8788 -> tm1)
                              | (uu____8789,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____8790))::
                                  (t,uu____8792)::[] ->
                                  let uu____8831 =
                                    let uu____8832 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____8832.FStar_Syntax_Syntax.n in
                                  (match uu____8831 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____8835::[],body,uu____8837) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____8864 -> tm1)
                                   | uu____8867 -> tm1)
                              | uu____8868 -> tm1
                            else
                              (let uu____8878 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.b2t_lid in
                               if uu____8878
                               then
                                 match args with
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (true ));
                                      FStar_Syntax_Syntax.pos = uu____8879;
                                      FStar_Syntax_Syntax.vars = uu____8880;_},uu____8881)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (false ));
                                      FStar_Syntax_Syntax.pos = uu____8898;
                                      FStar_Syntax_Syntax.vars = uu____8899;_},uu____8900)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | uu____8917 -> tm1
                               else reduce_equality cfg tm1))))))
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                FStar_Syntax_Syntax.pos = uu____8928;
                FStar_Syntax_Syntax.vars = uu____8929;_},args)
             ->
             let uu____8951 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
             if uu____8951
             then
               let uu____8952 =
                 FStar_All.pipe_right args (FStar_List.map simplify1) in
               (match uu____8952 with
                | (FStar_Pervasives_Native.Some (true ),uu____9007)::
                    (uu____9008,(arg,uu____9010))::[] -> arg
                | (uu____9075,(arg,uu____9077))::(FStar_Pervasives_Native.Some
                                                  (true ),uu____9078)::[]
                    -> arg
                | (FStar_Pervasives_Native.Some (false ),uu____9143)::uu____9144::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____9207::(FStar_Pervasives_Native.Some (false
                               ),uu____9208)::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____9271 -> tm1)
             else
               (let uu____9287 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
                if uu____9287
                then
                  let uu____9288 =
                    FStar_All.pipe_right args (FStar_List.map simplify1) in
                  match uu____9288 with
                  | (FStar_Pervasives_Native.Some (true ),uu____9343)::uu____9344::[]
                      -> w FStar_Syntax_Util.t_true
                  | uu____9407::(FStar_Pervasives_Native.Some (true
                                 ),uu____9408)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____9471)::
                      (uu____9472,(arg,uu____9474))::[] -> arg
                  | (uu____9539,(arg,uu____9541))::(FStar_Pervasives_Native.Some
                                                    (false ),uu____9542)::[]
                      -> arg
                  | uu____9607 -> tm1
                else
                  (let uu____9623 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.imp_lid in
                   if uu____9623
                   then
                     let uu____9624 =
                       FStar_All.pipe_right args (FStar_List.map simplify1) in
                     match uu____9624 with
                     | uu____9679::(FStar_Pervasives_Native.Some (true
                                    ),uu____9680)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____9743)::uu____9744::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____9807)::
                         (uu____9808,(arg,uu____9810))::[] -> arg
                     | (uu____9875,(p,uu____9877))::(uu____9878,(q,uu____9880))::[]
                         ->
                         let uu____9945 = FStar_Syntax_Util.term_eq p q in
                         (if uu____9945
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____9947 -> tm1
                   else
                     (let uu____9963 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____9963
                      then
                        let uu____9964 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1) in
                        match uu____9964 with
                        | (FStar_Pervasives_Native.Some (true ),uu____10019)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____10058)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____10097 -> tm1
                      else
                        (let uu____10113 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____10113
                         then
                           match args with
                           | (t,uu____10115)::[] ->
                               let uu____10132 =
                                 let uu____10133 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____10133.FStar_Syntax_Syntax.n in
                               (match uu____10132 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____10136::[],body,uu____10138) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____10165 -> tm1)
                                | uu____10168 -> tm1)
                           | (uu____10169,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____10170))::
                               (t,uu____10172)::[] ->
                               let uu____10211 =
                                 let uu____10212 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____10212.FStar_Syntax_Syntax.n in
                               (match uu____10211 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____10215::[],body,uu____10217) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____10244 -> tm1)
                                | uu____10247 -> tm1)
                           | uu____10248 -> tm1
                         else
                           (let uu____10258 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____10258
                            then
                              match args with
                              | (t,uu____10260)::[] ->
                                  let uu____10277 =
                                    let uu____10278 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____10278.FStar_Syntax_Syntax.n in
                                  (match uu____10277 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____10281::[],body,uu____10283) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____10310 -> tm1)
                                   | uu____10313 -> tm1)
                              | (uu____10314,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____10315))::
                                  (t,uu____10317)::[] ->
                                  let uu____10356 =
                                    let uu____10357 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____10357.FStar_Syntax_Syntax.n in
                                  (match uu____10356 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____10360::[],body,uu____10362) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____10389 -> tm1)
                                   | uu____10392 -> tm1)
                              | uu____10393 -> tm1
                            else
                              (let uu____10403 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.b2t_lid in
                               if uu____10403
                               then
                                 match args with
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (true ));
                                      FStar_Syntax_Syntax.pos = uu____10404;
                                      FStar_Syntax_Syntax.vars = uu____10405;_},uu____10406)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (false ));
                                      FStar_Syntax_Syntax.pos = uu____10423;
                                      FStar_Syntax_Syntax.vars = uu____10424;_},uu____10425)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | uu____10442 -> tm1
                               else reduce_equality cfg tm1))))))
         | uu____10452 -> tm1)
let is_norm_request:
  'Auu____10459 .
    FStar_Syntax_Syntax.term -> 'Auu____10459 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10472 =
        let uu____10479 =
          let uu____10480 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10480.FStar_Syntax_Syntax.n in
        (uu____10479, args) in
      match uu____10472 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10486::uu____10487::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10491::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10496::uu____10497::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10500 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___155_10512  ->
    match uu___155_10512 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.WHNF  -> [WHNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10518 =
          let uu____10521 =
            let uu____10522 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____10522 in
          [uu____10521] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10518
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____10541 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10541) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10579 =
          FStar_Syntax_Embeddings.unembed_list
            FStar_Syntax_Embeddings.unembed_norm_step s in
        FStar_All.pipe_left tr_norm_steps uu____10579 in
      match args with
      | uu____10592::(tm,uu____10594)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____10617)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____10632)::uu____10633::(tm,uu____10635)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____10675 =
              let uu____10678 = full_norm steps in parse_steps uu____10678 in
            Beta :: uu____10675 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____10687 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___156_10705  ->
    match uu___156_10705 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.pos = uu____10708;
           FStar_Syntax_Syntax.vars = uu____10709;_},uu____10710,uu____10711))::uu____10712
        -> true
    | uu____10719 -> false
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
            (fun uu____10854  ->
               let uu____10855 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____10856 = FStar_Syntax_Print.term_to_string t1 in
               let uu____10857 =
                 let uu____10858 =
                   let uu____10861 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____10861 in
                 stack_to_string uu____10858 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____10855
                 uu____10856 uu____10857);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____10884 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____10909 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____10926 =
                 let uu____10927 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____10928 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____10927 uu____10928 in
               failwith uu____10926
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____10929 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____10946 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____10947 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10948;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____10949;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10952;
                 FStar_Syntax_Syntax.fv_delta = uu____10953;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10954;
                 FStar_Syntax_Syntax.fv_delta = uu____10955;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____10956);_}
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
                 let uu___188_10998 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___188_10998.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___188_10998.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____11031 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____11031) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___189_11039 = cfg in
                 let uu____11040 =
                   FStar_List.filter
                     (fun uu___157_11043  ->
                        match uu___157_11043 with
                        | UnfoldOnly uu____11044 -> false
                        | NoDeltaSteps  -> false
                        | uu____11047 -> true) cfg.steps in
                 {
                   steps = uu____11040;
                   tcenv = (uu___189_11039.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___189_11039.primitive_steps)
                 } in
               let uu____11048 = get_norm_request (norm cfg' env []) args in
               (match uu____11048 with
                | (s,tm) ->
                    let delta_level =
                      let uu____11064 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___158_11069  ->
                                match uu___158_11069 with
                                | UnfoldUntil uu____11070 -> true
                                | UnfoldOnly uu____11071 -> true
                                | uu____11074 -> false)) in
                      if uu____11064
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___190_11079 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___190_11079.tcenv);
                        delta_level;
                        primitive_steps = (uu___190_11079.primitive_steps)
                      } in
                    let stack' =
                      let tail1 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let uu____11090 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____11090
                      then
                        let uu____11093 =
                          let uu____11094 =
                            let uu____11099 = FStar_Util.now () in
                            (t1, uu____11099) in
                          Debug uu____11094 in
                        uu____11093 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11101;
                  FStar_Syntax_Syntax.vars = uu____11102;_},a1::a2::rest)
               ->
               let uu____11150 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11150 with
                | (hd1,uu____11166) ->
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
                    (FStar_Const.Const_reflect uu____11231);
                  FStar_Syntax_Syntax.pos = uu____11232;
                  FStar_Syntax_Syntax.vars = uu____11233;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____11265 = FStar_List.tl stack1 in
               norm cfg env uu____11265 (FStar_Pervasives_Native.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11268;
                  FStar_Syntax_Syntax.vars = uu____11269;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____11301 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11301 with
                | (reify_head,uu____11317) ->
                    let a1 =
                      let uu____11339 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (FStar_Pervasives_Native.fst a) in
                      FStar_Syntax_Subst.compress uu____11339 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____11342);
                            FStar_Syntax_Syntax.pos = uu____11343;
                            FStar_Syntax_Syntax.vars = uu____11344;_},a2::[])
                         ->
                         norm cfg env stack1 (FStar_Pervasives_Native.fst a2)
                     | uu____11378 ->
                         let stack2 =
                           (App
                              (reify_head, FStar_Pervasives_Native.None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11388 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____11388
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11395 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11395
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____11398 =
                      let uu____11405 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11405, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11398 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___159_11419  ->
                         match uu___159_11419 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11422 =
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
                 if uu____11422
                 then false
                 else
                   (let uu____11424 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___160_11431  ->
                              match uu___160_11431 with
                              | UnfoldOnly uu____11432 -> true
                              | uu____11435 -> false)) in
                    match uu____11424 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11439 -> should_delta) in
               (log cfg
                  (fun uu____11447  ->
                     let uu____11448 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11449 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____11450 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11448 uu____11449 uu____11450);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack1 t1
                else
                  (let r_env =
                     let uu____11453 = FStar_Syntax_Syntax.range_of_fv f in
                     FStar_TypeChecker_Env.set_range cfg.tcenv uu____11453 in
                   let uu____11454 =
                     FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                       r_env
                       (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   match uu____11454 with
                   | FStar_Pervasives_Native.None  ->
                       (log cfg
                          (fun uu____11467  ->
                             FStar_Util.print "Tm_fvar case 2\n" []);
                        rebuild cfg env stack1 t1)
                   | FStar_Pervasives_Native.Some (us,t2) ->
                       (log cfg
                          (fun uu____11478  ->
                             let uu____11479 =
                               FStar_Syntax_Print.term_to_string t0 in
                             let uu____11480 =
                               FStar_Syntax_Print.term_to_string t2 in
                             FStar_Util.print2 ">>> Unfolded %s to %s\n"
                               uu____11479 uu____11480);
                        (let t3 =
                           let uu____11482 =
                             FStar_All.pipe_right cfg.steps
                               (FStar_List.contains
                                  (UnfoldUntil
                                     FStar_Syntax_Syntax.Delta_constant)) in
                           if uu____11482
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
                           | (UnivArgs (us',uu____11492))::stack2 ->
                               let env1 =
                                 FStar_All.pipe_right us'
                                   (FStar_List.fold_left
                                      (fun env1  ->
                                         fun u  -> (Univ u) :: env1) env) in
                               norm cfg env1 stack2 t3
                           | uu____11515 when
                               FStar_All.pipe_right cfg.steps
                                 (FStar_List.contains EraseUniverses)
                               -> norm cfg env stack1 t3
                           | uu____11516 ->
                               let uu____11517 =
                                 let uu____11518 =
                                   FStar_Syntax_Print.lid_to_string
                                     (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                 FStar_Util.format1
                                   "Impossible: missing universe instantiation on %s"
                                   uu____11518 in
                               failwith uu____11517
                         else norm cfg env stack1 t3))))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11521 = lookup_bvar env x in
               (match uu____11521 with
                | Univ uu____11522 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11547 = FStar_ST.op_Bang r in
                      (match uu____11547 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11628  ->
                                 let uu____11629 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____11630 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11629
                                   uu____11630);
                            (let uu____11631 =
                               let uu____11632 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____11632.FStar_Syntax_Syntax.n in
                             match uu____11631 with
                             | FStar_Syntax_Syntax.Tm_abs uu____11635 ->
                                 norm cfg env2 stack1 t'
                             | uu____11652 -> rebuild cfg env2 stack1 t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____11704)::uu____11705 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11714)::uu____11715 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11725,uu____11726))::stack_rest ->
                    (match c with
                     | Univ uu____11730 -> norm cfg (c :: env) stack_rest t1
                     | uu____11731 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____11736::[] ->
                              (log cfg
                                 (fun uu____11752  ->
                                    let uu____11753 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11753);
                               norm cfg (c :: env) stack_rest body)
                          | uu____11754::tl1 ->
                              (log cfg
                                 (fun uu____11773  ->
                                    let uu____11774 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11774);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___191_11804 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___191_11804.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____11865  ->
                          let uu____11866 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11866);
                     norm cfg env stack2 t1)
                | (Debug uu____11867)::uu____11868 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11875 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11875
                    else
                      (let uu____11877 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11877 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11901  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11917 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11917
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11927 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11927)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___192_11932 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___192_11932.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___192_11932.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11933 -> lopt in
                           (log cfg
                              (fun uu____11939  ->
                                 let uu____11940 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11940);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___193_11953 = cfg in
                               let uu____11954 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___193_11953.steps);
                                 tcenv = (uu___193_11953.tcenv);
                                 delta_level = (uu___193_11953.delta_level);
                                 primitive_steps = uu____11954
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____11963)::uu____11964 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11971 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11971
                    else
                      (let uu____11973 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11973 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11997  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12013 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12013
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12023 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12023)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___192_12028 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___192_12028.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___192_12028.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12029 -> lopt in
                           (log cfg
                              (fun uu____12035  ->
                                 let uu____12036 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12036);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___193_12049 = cfg in
                               let uu____12050 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___193_12049.steps);
                                 tcenv = (uu___193_12049.tcenv);
                                 delta_level = (uu___193_12049.delta_level);
                                 primitive_steps = uu____12050
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____12059)::uu____12060 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12071 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12071
                    else
                      (let uu____12073 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12073 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12097  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12113 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12113
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12123 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12123)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___192_12128 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___192_12128.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___192_12128.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12129 -> lopt in
                           (log cfg
                              (fun uu____12135  ->
                                 let uu____12136 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12136);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___193_12149 = cfg in
                               let uu____12150 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___193_12149.steps);
                                 tcenv = (uu___193_12149.tcenv);
                                 delta_level = (uu___193_12149.delta_level);
                                 primitive_steps = uu____12150
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____12159)::uu____12160 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12169 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12169
                    else
                      (let uu____12171 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12171 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12195  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12211 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12211
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12221 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12221)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___192_12226 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___192_12226.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___192_12226.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12227 -> lopt in
                           (log cfg
                              (fun uu____12233  ->
                                 let uu____12234 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12234);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___193_12247 = cfg in
                               let uu____12248 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___193_12247.steps);
                                 tcenv = (uu___193_12247.tcenv);
                                 delta_level = (uu___193_12247.delta_level);
                                 primitive_steps = uu____12248
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____12257)::uu____12258 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12273 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12273
                    else
                      (let uu____12275 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12275 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12299  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12315 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12315
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12325 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12325)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___192_12330 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___192_12330.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___192_12330.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12331 -> lopt in
                           (log cfg
                              (fun uu____12337  ->
                                 let uu____12338 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12338);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___193_12351 = cfg in
                               let uu____12352 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___193_12351.steps);
                                 tcenv = (uu___193_12351.tcenv);
                                 delta_level = (uu___193_12351.delta_level);
                                 primitive_steps = uu____12352
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12361 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12361
                    else
                      (let uu____12363 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12363 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12387  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12403 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12403
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12413 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12413)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___192_12418 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___192_12418.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___192_12418.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12419 -> lopt in
                           (log cfg
                              (fun uu____12425  ->
                                 let uu____12426 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12426);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___193_12439 = cfg in
                               let uu____12440 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___193_12439.steps);
                                 tcenv = (uu___193_12439.tcenv);
                                 delta_level = (uu___193_12439.delta_level);
                                 primitive_steps = uu____12440
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
                      (fun uu____12487  ->
                         fun stack2  ->
                           match uu____12487 with
                           | (a,aq) ->
                               let uu____12499 =
                                 let uu____12500 =
                                   let uu____12507 =
                                     let uu____12508 =
                                       let uu____12527 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____12527, false) in
                                     Clos uu____12508 in
                                   (uu____12507, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____12500 in
                               uu____12499 :: stack2) args) in
               (log cfg
                  (fun uu____12579  ->
                     let uu____12580 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12580);
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
                             ((let uu___194_12604 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___194_12604.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___194_12604.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____12605 ->
                      let uu____12610 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12610)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____12613 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____12613 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____12638 =
                          let uu____12639 =
                            let uu____12646 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___195_12648 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___195_12648.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___195_12648.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12646) in
                          FStar_Syntax_Syntax.Tm_refine uu____12639 in
                        mk uu____12638 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____12667 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____12667
               else
                 (let uu____12669 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____12669 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12677 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12689  -> Dummy :: env1) env) in
                        norm_comp cfg uu____12677 c1 in
                      let t2 =
                        let uu____12699 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____12699 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____12758)::uu____12759 -> norm cfg env stack1 t11
                | (Arg uu____12768)::uu____12769 -> norm cfg env stack1 t11
                | (App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____12778;
                       FStar_Syntax_Syntax.vars = uu____12779;_},uu____12780,uu____12781))::uu____12782
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____12789)::uu____12790 ->
                    norm cfg env stack1 t11
                | uu____12799 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____12803  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____12820 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____12820
                        | FStar_Util.Inr c ->
                            let uu____12828 = norm_comp cfg env c in
                            FStar_Util.Inr uu____12828 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____12834 =
                        let uu____12835 =
                          let uu____12836 =
                            let uu____12863 = FStar_Syntax_Util.unascribe t12 in
                            (uu____12863, (tc1, tacopt1), l) in
                          FStar_Syntax_Syntax.Tm_ascribed uu____12836 in
                        mk uu____12835 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____12834)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____12939,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____12940;
                               FStar_Syntax_Syntax.lbunivs = uu____12941;
                               FStar_Syntax_Syntax.lbtyp = uu____12942;
                               FStar_Syntax_Syntax.lbeff = uu____12943;
                               FStar_Syntax_Syntax.lbdef = uu____12944;_}::uu____12945),uu____12946)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____12982 =
                 (let uu____12985 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____12985) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____12987 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____12987))) in
               if uu____12982
               then
                 let env1 =
                   let uu____12991 =
                     let uu____12992 =
                       let uu____13011 =
                         FStar_Util.mk_ref FStar_Pervasives_Native.None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____13011,
                         false) in
                     Clos uu____12992 in
                   uu____12991 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____13063 =
                    let uu____13068 =
                      let uu____13069 =
                        let uu____13070 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____13070
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____13069] in
                    FStar_Syntax_Subst.open_term uu____13068 body in
                  match uu____13063 with
                  | (bs,body1) ->
                      let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                      let lbname =
                        let x =
                          let uu____13084 = FStar_List.hd bs in
                          FStar_Pervasives_Native.fst uu____13084 in
                        FStar_Util.Inl
                          (let uu___196_13094 = x in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___196_13094.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___196_13094.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = ty
                           }) in
                      let lb1 =
                        let uu___197_13096 = lb in
                        let uu____13097 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = lbname;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___197_13096.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = ty;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___197_13096.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____13097
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____13114  -> Dummy :: env1)
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
               let uu____13137 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____13137 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____13173 =
                               let uu___198_13174 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___198_13174.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___198_13174.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____13173 in
                           let uu____13175 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____13175 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____13195 =
                                   FStar_List.map (fun uu____13199  -> Dummy)
                                     lbs1 in
                                 let uu____13200 =
                                   let uu____13203 =
                                     FStar_List.map
                                       (fun uu____13211  -> Dummy) xs1 in
                                   FStar_List.append uu____13203 env in
                                 FStar_List.append uu____13195 uu____13200 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13223 =
                                       let uu___199_13224 = rc in
                                       let uu____13225 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___199_13224.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13225;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___199_13224.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____13223
                                 | uu____13232 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___200_13236 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___200_13236.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___200_13236.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____13240 =
                        FStar_List.map (fun uu____13244  -> Dummy) lbs2 in
                      FStar_List.append uu____13240 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____13246 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____13246 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___201_13262 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___201_13262.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___201_13262.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____13289 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____13289
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13308 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13359  ->
                        match uu____13359 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____13432 =
                                let uu___202_13433 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___202_13433.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___202_13433.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____13432 in
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
               (match uu____13308 with
                | (rec_env,memos,uu____13561) ->
                    let uu____13590 =
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
                             let uu____13995 =
                               let uu____13996 =
                                 let uu____14015 =
                                   FStar_Util.mk_ref
                                     FStar_Pervasives_Native.None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____14015, false) in
                               Clos uu____13996 in
                             uu____13995 :: env1)
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
                             FStar_Syntax_Syntax.pos = uu____14083;
                             FStar_Syntax_Syntax.vars = uu____14084;_},uu____14085,uu____14086))::uu____14087
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____14094 -> false in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____14104 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____14104
                        then
                          let uu___203_14105 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___203_14105.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps =
                              (uu___203_14105.primitive_steps)
                          }
                        else
                          (let uu___204_14107 = cfg in
                           {
                             steps =
                               (FStar_List.append [Exclude Zeta] cfg.steps);
                             tcenv = (uu___204_14107.tcenv);
                             delta_level = (uu___204_14107.delta_level);
                             primitive_steps =
                               (uu___204_14107.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____14109 =
                         let uu____14110 = FStar_Syntax_Subst.compress head1 in
                         uu____14110.FStar_Syntax_Syntax.n in
                       match uu____14109 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____14128 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____14128 with
                            | (uu____14129,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____14135 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____14143 =
                                         let uu____14144 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____14144.FStar_Syntax_Syntax.n in
                                       match uu____14143 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____14150,uu____14151))
                                           ->
                                           let uu____14160 =
                                             let uu____14161 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____14161.FStar_Syntax_Syntax.n in
                                           (match uu____14160 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____14167,msrc,uu____14169))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____14178 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14178
                                            | uu____14179 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____14180 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____14181 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____14181 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___205_14186 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___205_14186.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___205_14186.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___205_14186.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____14187 =
                                            FStar_List.tl stack1 in
                                          let uu____14188 =
                                            let uu____14189 =
                                              let uu____14192 =
                                                let uu____14193 =
                                                  let uu____14206 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____14206) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____14193 in
                                              FStar_Syntax_Syntax.mk
                                                uu____14192 in
                                            uu____14189
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____14187
                                            uu____14188
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____14222 =
                                            let uu____14223 = is_return body in
                                            match uu____14223 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____14227;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____14228;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____14233 -> false in
                                          if uu____14222
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
                                               let uu____14257 =
                                                 let uu____14260 =
                                                   let uu____14261 =
                                                     let uu____14278 =
                                                       let uu____14281 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____14281] in
                                                     (uu____14278, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc)) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____14261 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____14260 in
                                               uu____14257
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____14297 =
                                                 let uu____14298 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____14298.FStar_Syntax_Syntax.n in
                                               match uu____14297 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____14304::uu____14305::[])
                                                   ->
                                                   let uu____14312 =
                                                     let uu____14315 =
                                                       let uu____14316 =
                                                         let uu____14323 =
                                                           let uu____14326 =
                                                             let uu____14327
                                                               =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____14327 in
                                                           let uu____14328 =
                                                             let uu____14331
                                                               =
                                                               let uu____14332
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____14332 in
                                                             [uu____14331] in
                                                           uu____14326 ::
                                                             uu____14328 in
                                                         (bind1, uu____14323) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____14316 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____14315 in
                                                   uu____14312
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____14340 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____14346 =
                                                 let uu____14349 =
                                                   let uu____14350 =
                                                     let uu____14365 =
                                                       let uu____14368 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____14369 =
                                                         let uu____14372 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____14373 =
                                                           let uu____14376 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____14377 =
                                                             let uu____14380
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____14381
                                                               =
                                                               let uu____14384
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____14385
                                                                 =
                                                                 let uu____14388
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____14388] in
                                                               uu____14384 ::
                                                                 uu____14385 in
                                                             uu____14380 ::
                                                               uu____14381 in
                                                           uu____14376 ::
                                                             uu____14377 in
                                                         uu____14372 ::
                                                           uu____14373 in
                                                       uu____14368 ::
                                                         uu____14369 in
                                                     (bind_inst, uu____14365) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____14350 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____14349 in
                                               uu____14346
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____14396 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____14396 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____14420 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____14420 with
                            | (uu____14421,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____14450 =
                                        let uu____14451 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____14451.FStar_Syntax_Syntax.n in
                                      match uu____14450 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____14457) -> t4
                                      | uu____14462 -> head2 in
                                    let uu____14463 =
                                      let uu____14464 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____14464.FStar_Syntax_Syntax.n in
                                    match uu____14463 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____14470 ->
                                        FStar_Pervasives_Native.None in
                                  let uu____14471 = maybe_extract_fv head2 in
                                  match uu____14471 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____14481 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____14481
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____14486 =
                                          maybe_extract_fv head3 in
                                        match uu____14486 with
                                        | FStar_Pervasives_Native.Some
                                            uu____14491 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____14492 ->
                                            FStar_Pervasives_Native.Some
                                              false in
                                      (head3, action_unfolded)
                                  | uu____14497 ->
                                      (head2, FStar_Pervasives_Native.None) in
                                ((let is_arg_impure uu____14512 =
                                    match uu____14512 with
                                    | (e,q) ->
                                        let uu____14519 =
                                          let uu____14520 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____14520.FStar_Syntax_Syntax.n in
                                        (match uu____14519 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____14535 -> false) in
                                  let uu____14536 =
                                    let uu____14537 =
                                      let uu____14544 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____14544 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____14537 in
                                  if uu____14536
                                  then
                                    let uu____14549 =
                                      let uu____14550 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____14550 in
                                    failwith uu____14549
                                  else ());
                                 (let uu____14552 =
                                    maybe_unfold_action head_app in
                                  match uu____14552 with
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
                                      let uu____14591 = FStar_List.tl stack1 in
                                      norm cfg env uu____14591 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____14605 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____14605 in
                           let uu____14606 = FStar_List.tl stack1 in
                           norm cfg env uu____14606 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____14727  ->
                                     match uu____14727 with
                                     | (pat,wopt,tm) ->
                                         let uu____14775 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____14775))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____14807 = FStar_List.tl stack1 in
                           norm cfg env uu____14807 tm
                       | uu____14808 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.pos = uu____14817;
                             FStar_Syntax_Syntax.vars = uu____14818;_},uu____14819,uu____14820))::uu____14821
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____14828 -> false in
                    if should_reify
                    then
                      let uu____14829 = FStar_List.tl stack1 in
                      let uu____14830 =
                        let uu____14831 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____14831 in
                      norm cfg env uu____14829 uu____14830
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____14834 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____14834
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___206_14843 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___206_14843.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___206_14843.primitive_steps)
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
                | uu____14845 ->
                    if FStar_List.contains Unmeta cfg.steps
                    then norm cfg env stack1 head1
                    else
                      (match stack1 with
                       | uu____14847::uu____14848 ->
                           (match m with
                            | FStar_Syntax_Syntax.Meta_labeled
                                (l,r,uu____14853) ->
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
                            | uu____14878 -> norm cfg env stack1 head1)
                       | [] ->
                           let head2 = norm cfg env [] head1 in
                           let m1 =
                             match m with
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let uu____14892 =
                                   norm_pattern_args cfg env args in
                                 FStar_Syntax_Syntax.Meta_pattern uu____14892
                             | uu____14903 -> m in
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
              let uu____14915 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____14915 with
              | (uu____14916,return_repr) ->
                  let return_inst =
                    let uu____14925 =
                      let uu____14926 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____14926.FStar_Syntax_Syntax.n in
                    match uu____14925 with
                    | FStar_Syntax_Syntax.Tm_uinst
                        (return_tm,uu____14932::[]) ->
                        let uu____14939 =
                          let uu____14942 =
                            let uu____14943 =
                              let uu____14950 =
                                let uu____14953 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____14953] in
                              (return_tm, uu____14950) in
                            FStar_Syntax_Syntax.Tm_uinst uu____14943 in
                          FStar_Syntax_Syntax.mk uu____14942 in
                        uu____14939 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____14961 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____14964 =
                    let uu____14967 =
                      let uu____14968 =
                        let uu____14983 =
                          let uu____14986 = FStar_Syntax_Syntax.as_arg t in
                          let uu____14987 =
                            let uu____14990 = FStar_Syntax_Syntax.as_arg e in
                            [uu____14990] in
                          uu____14986 :: uu____14987 in
                        (return_inst, uu____14983) in
                      FStar_Syntax_Syntax.Tm_app uu____14968 in
                    FStar_Syntax_Syntax.mk uu____14967 in
                  uu____14964 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____14999 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____14999 with
               | FStar_Pervasives_Native.None  ->
                   let uu____15002 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____15002
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____15003;
                     FStar_TypeChecker_Env.mtarget = uu____15004;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____15005;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____15016;
                     FStar_TypeChecker_Env.mtarget = uu____15017;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____15018;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____15036 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____15036)
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
                (fun uu____15092  ->
                   match uu____15092 with
                   | (a,imp) ->
                       let uu____15103 = norm cfg env [] a in
                       (uu____15103, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___207_15120 = comp1 in
            let uu____15123 =
              let uu____15124 =
                let uu____15133 = norm cfg env [] t in
                let uu____15134 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____15133, uu____15134) in
              FStar_Syntax_Syntax.Total uu____15124 in
            {
              FStar_Syntax_Syntax.n = uu____15123;
              FStar_Syntax_Syntax.pos =
                (uu___207_15120.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___207_15120.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___208_15149 = comp1 in
            let uu____15152 =
              let uu____15153 =
                let uu____15162 = norm cfg env [] t in
                let uu____15163 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____15162, uu____15163) in
              FStar_Syntax_Syntax.GTotal uu____15153 in
            {
              FStar_Syntax_Syntax.n = uu____15152;
              FStar_Syntax_Syntax.pos =
                (uu___208_15149.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___208_15149.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____15215  ->
                      match uu____15215 with
                      | (a,i) ->
                          let uu____15226 = norm cfg env [] a in
                          (uu____15226, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___161_15237  ->
                      match uu___161_15237 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____15241 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____15241
                      | f -> f)) in
            let uu___209_15245 = comp1 in
            let uu____15248 =
              let uu____15249 =
                let uu___210_15250 = ct in
                let uu____15251 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____15252 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____15255 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____15251;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___210_15250.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____15252;
                  FStar_Syntax_Syntax.effect_args = uu____15255;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____15249 in
            {
              FStar_Syntax_Syntax.n = uu____15248;
              FStar_Syntax_Syntax.pos =
                (uu___209_15245.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___209_15245.FStar_Syntax_Syntax.vars)
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
            (let uu___211_15273 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___211_15273.tcenv);
               delta_level = (uu___211_15273.delta_level);
               primitive_steps = (uu___211_15273.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____15278 = norm1 t in
          FStar_Syntax_Util.non_informative uu____15278 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____15281 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___212_15300 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.pos =
                (uu___212_15300.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___212_15300.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____15307 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____15307
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
                    let uu___213_15318 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___213_15318.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___213_15318.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___213_15318.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___214_15320 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___214_15320.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___214_15320.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___214_15320.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___214_15320.FStar_Syntax_Syntax.flags)
                    } in
              let uu___215_15321 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos =
                  (uu___215_15321.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___215_15321.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____15323 -> c
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____15326  ->
        match uu____15326 with
        | (x,imp) ->
            let uu____15329 =
              let uu___216_15330 = x in
              let uu____15331 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___216_15330.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___216_15330.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____15331
              } in
            (uu____15329, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____15337 =
          FStar_List.fold_left
            (fun uu____15355  ->
               fun b  ->
                 match uu____15355 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____15337 with | (nbs,uu____15383) -> FStar_List.rev nbs
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
            let uu____15399 =
              let uu___217_15400 = rc in
              let uu____15401 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___217_15400.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____15401;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___217_15400.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____15399
        | uu____15408 -> lopt
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
              ((let uu____15421 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____15421
                then
                  let time_now = FStar_Util.now () in
                  let uu____15423 =
                    let uu____15424 =
                      let uu____15425 =
                        FStar_Util.time_diff time_then time_now in
                      FStar_Pervasives_Native.snd uu____15425 in
                    FStar_Util.string_of_int uu____15424 in
                  let uu____15430 = FStar_Syntax_Print.term_to_string tm in
                  let uu____15431 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                    uu____15423 uu____15430 uu____15431
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___218_15449 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___218_15449.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____15518  ->
                    let uu____15519 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____15519);
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
              let uu____15555 =
                let uu___219_15556 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___219_15556.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___219_15556.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____15555
          | (Arg (Univ uu____15557,uu____15558,uu____15559))::uu____15560 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____15563,uu____15564))::uu____15565 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____15581),aq,r))::stack2 ->
              (log cfg
                 (fun uu____15610  ->
                    let uu____15611 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____15611);
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
                 (let uu____15621 = FStar_ST.op_Bang m in
                  match uu____15621 with
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
                  | FStar_Pervasives_Native.Some (uu____15721,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq)
                          FStar_Pervasives_Native.None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 =
                FStar_Syntax_Syntax.extend_app head1 (t, aq)
                  FStar_Pervasives_Native.None r in
              let uu____15745 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____15745
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____15755  ->
                    let uu____15756 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____15756);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____15761 =
                  log cfg
                    (fun uu____15766  ->
                       let uu____15767 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____15768 =
                         let uu____15769 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____15786  ->
                                   match uu____15786 with
                                   | (p,uu____15796,uu____15797) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____15769
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____15767 uu____15768);
                  (let whnf1 = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___162_15814  ->
                               match uu___162_15814 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____15815 -> false)) in
                     let steps' =
                       let uu____15819 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____15819
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___220_15823 = cfg in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___220_15823.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___220_15823.primitive_steps)
                     } in
                   let norm_or_whnf env2 t1 =
                     if whnf1
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____15867 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____15890 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____15956  ->
                                   fun uu____15957  ->
                                     match (uu____15956, uu____15957) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____16060 = norm_pat env3 p1 in
                                         (match uu____16060 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____15890 with
                          | (pats1,env3) ->
                              ((let uu___221_16162 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.p =
                                    (uu___221_16162.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___222_16181 = x in
                           let uu____16182 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___222_16181.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___222_16181.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16182
                           } in
                         ((let uu___223_16190 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.p =
                               (uu___223_16190.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___224_16195 = x in
                           let uu____16196 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___224_16195.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___224_16195.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16196
                           } in
                         ((let uu___225_16204 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.p =
                               (uu___225_16204.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___226_16214 = x in
                           let uu____16215 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___226_16214.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___226_16214.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16215
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___227_16224 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.p =
                               (uu___227_16224.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf1 -> branches
                     | uu____16228 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____16242 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____16242 with
                                 | (p,wopt,e) ->
                                     let uu____16262 = norm_pat env1 p in
                                     (match uu____16262 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Pervasives_Native.Some w
                                                ->
                                                let uu____16293 =
                                                  norm_or_whnf env2 w in
                                                FStar_Pervasives_Native.Some
                                                  uu____16293 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____16299 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____16299) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____16309) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____16314 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____16315;
                        FStar_Syntax_Syntax.fv_delta = uu____16316;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Data_ctor );_}
                      -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____16317;
                        FStar_Syntax_Syntax.fv_delta = uu____16318;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Record_ctor uu____16319);_}
                      -> true
                  | uu____16326 -> false in
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
                  let uu____16455 =
                    FStar_Syntax_Util.head_and_args scrutinee1 in
                  match uu____16455 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var uu____16504 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_wild uu____16507 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____16510 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee1.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____16529 ->
                                let uu____16530 =
                                  let uu____16531 = is_cons head1 in
                                  Prims.op_Negation uu____16531 in
                                FStar_Util.Inr uu____16530)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____16552 =
                             let uu____16553 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____16553.FStar_Syntax_Syntax.n in
                           (match uu____16552 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____16563 ->
                                let uu____16564 =
                                  let uu____16565 = is_cons head1 in
                                  Prims.op_Negation uu____16565 in
                                FStar_Util.Inr uu____16564))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____16618)::rest_a,(p1,uu____16621)::rest_p) ->
                      let uu____16665 = matches_pat t1 p1 in
                      (match uu____16665 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____16690 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____16792 = matches_pat scrutinee1 p1 in
                      (match uu____16792 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____16812  ->
                                 let uu____16813 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____16814 =
                                   let uu____16815 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____16815
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____16813 uu____16814);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____16832 =
                                        let uu____16833 =
                                          let uu____16852 =
                                            FStar_Util.mk_ref
                                              (FStar_Pervasives_Native.Some
                                                 ([], t1)) in
                                          ([], t1, uu____16852, false) in
                                        Clos uu____16833 in
                                      uu____16832 :: env2) env1 s in
                             let uu____16905 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____16905))) in
                let uu____16906 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____16906
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___163_16929  ->
                match uu___163_16929 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____16933 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____16939 -> d in
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
            let uu___228_16968 = config s e in
            {
              steps = (uu___228_16968.steps);
              tcenv = (uu___228_16968.tcenv);
              delta_level = (uu___228_16968.delta_level);
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
      fun t  -> let uu____16993 = config s e in norm_comp uu____16993 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____17002 = config [] env in norm_universe uu____17002 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let uu____17011 = config [] env in ghost_to_pure_aux uu____17011 [] c
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
        let uu____17025 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____17025 in
      let uu____17026 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____17026
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___229_17028 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___229_17028.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___229_17028.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____17031  ->
                    let uu____17032 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____17032))
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
            ((let uu____17051 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____17051);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____17064 = config [AllowUnboundUniverses] env in
          norm_comp uu____17064 [] c
        with
        | e ->
            ((let uu____17071 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____17071);
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
                   let uu____17111 =
                     let uu____17112 =
                       let uu____17119 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____17119) in
                     FStar_Syntax_Syntax.Tm_refine uu____17112 in
                   mk uu____17111 t01.FStar_Syntax_Syntax.pos
               | uu____17124 -> t2)
          | uu____17125 -> t2 in
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
        let uu____17177 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____17177 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____17206 ->
                 let uu____17213 = FStar_Syntax_Util.abs_formals e in
                 (match uu____17213 with
                  | (actuals,uu____17223,uu____17224) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____17238 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____17238 with
                         | (binders,args) ->
                             let uu____17255 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____17255
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
      | uu____17265 ->
          let uu____17266 = FStar_Syntax_Util.head_and_args t in
          (match uu____17266 with
           | (head1,args) ->
               let uu____17303 =
                 let uu____17304 = FStar_Syntax_Subst.compress head1 in
                 uu____17304.FStar_Syntax_Syntax.n in
               (match uu____17303 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____17307,thead) ->
                    let uu____17333 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____17333 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____17375 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___234_17383 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___234_17383.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___234_17383.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___234_17383.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___234_17383.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___234_17383.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___234_17383.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___234_17383.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___234_17383.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___234_17383.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___234_17383.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___234_17383.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___234_17383.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___234_17383.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___234_17383.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___234_17383.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___234_17383.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___234_17383.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___234_17383.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___234_17383.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___234_17383.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___234_17383.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___234_17383.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___234_17383.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___234_17383.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___234_17383.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___234_17383.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___234_17383.FStar_TypeChecker_Env.identifier_info)
                                 }) t in
                            match uu____17375 with
                            | (uu____17384,ty,uu____17386) ->
                                eta_expand_with_type env t ty))
                | uu____17387 ->
                    let uu____17388 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___235_17396 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___235_17396.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___235_17396.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___235_17396.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___235_17396.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___235_17396.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___235_17396.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___235_17396.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___235_17396.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___235_17396.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___235_17396.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___235_17396.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___235_17396.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___235_17396.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___235_17396.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___235_17396.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___235_17396.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___235_17396.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___235_17396.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___235_17396.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___235_17396.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.type_of =
                             (uu___235_17396.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___235_17396.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___235_17396.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___235_17396.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___235_17396.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___235_17396.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___235_17396.FStar_TypeChecker_Env.identifier_info)
                         }) t in
                    (match uu____17388 with
                     | (uu____17397,ty,uu____17399) ->
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
            | (uu____17477,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____17483,FStar_Util.Inl t) ->
                let uu____17489 =
                  let uu____17492 =
                    let uu____17493 =
                      let uu____17506 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____17506) in
                    FStar_Syntax_Syntax.Tm_arrow uu____17493 in
                  FStar_Syntax_Syntax.mk uu____17492 in
                uu____17489 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____17510 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____17510 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____17537 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____17592 ->
                    let uu____17593 =
                      let uu____17602 =
                        let uu____17603 = FStar_Syntax_Subst.compress t3 in
                        uu____17603.FStar_Syntax_Syntax.n in
                      (uu____17602, tc) in
                    (match uu____17593 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____17628) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____17665) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____17704,FStar_Util.Inl uu____17705) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____17728 -> failwith "Impossible") in
              (match uu____17537 with
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
          let uu____17837 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____17837 with
          | (univ_names1,binders1,tc) ->
              let uu____17895 = FStar_Util.left tc in
              (univ_names1, binders1, uu____17895)
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
          let uu____17934 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____17934 with
          | (univ_names1,binders1,tc) ->
              let uu____17994 = FStar_Util.right tc in
              (univ_names1, binders1, uu____17994)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____18029 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____18029 with
           | (univ_names1,binders1,typ1) ->
               let uu___236_18057 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___236_18057.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___236_18057.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___236_18057.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___236_18057.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___237_18078 = s in
          let uu____18079 =
            let uu____18080 =
              let uu____18089 = FStar_List.map (elim_uvars env) sigs in
              (uu____18089, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____18080 in
          {
            FStar_Syntax_Syntax.sigel = uu____18079;
            FStar_Syntax_Syntax.sigrng =
              (uu___237_18078.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___237_18078.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___237_18078.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___237_18078.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____18106 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____18106 with
           | (univ_names1,uu____18124,typ1) ->
               let uu___238_18138 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___238_18138.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___238_18138.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___238_18138.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___238_18138.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____18144 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____18144 with
           | (univ_names1,uu____18162,typ1) ->
               let uu___239_18176 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___239_18176.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___239_18176.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___239_18176.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___239_18176.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____18210 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____18210 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____18233 =
                            let uu____18234 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____18234 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____18233 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___240_18237 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___240_18237.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___240_18237.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___241_18238 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___241_18238.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___241_18238.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___241_18238.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___241_18238.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___242_18250 = s in
          let uu____18251 =
            let uu____18252 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____18252 in
          {
            FStar_Syntax_Syntax.sigel = uu____18251;
            FStar_Syntax_Syntax.sigrng =
              (uu___242_18250.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___242_18250.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___242_18250.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___242_18250.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____18256 = elim_uvars_aux_t env us [] t in
          (match uu____18256 with
           | (us1,uu____18274,t1) ->
               let uu___243_18288 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___243_18288.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___243_18288.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___243_18288.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___243_18288.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____18289 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____18291 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____18291 with
           | (univs1,binders,signature) ->
               let uu____18319 =
                 let uu____18328 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____18328 with
                 | (univs_opening,univs2) ->
                     let uu____18355 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____18355) in
               (match uu____18319 with
                | (univs_opening,univs_closing) ->
                    let uu____18372 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____18378 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____18379 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____18378, uu____18379) in
                    (match uu____18372 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____18401 =
                           match uu____18401 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____18419 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____18419 with
                                | (us1,t1) ->
                                    let uu____18430 =
                                      let uu____18435 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____18442 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____18435, uu____18442) in
                                    (match uu____18430 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____18455 =
                                           let uu____18460 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____18469 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____18460, uu____18469) in
                                         (match uu____18455 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____18485 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____18485 in
                                              let uu____18486 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____18486 with
                                               | (uu____18507,uu____18508,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____18523 =
                                                       let uu____18524 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____18524 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____18523 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____18529 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____18529 with
                           | (uu____18542,uu____18543,t1) -> t1 in
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
                             | uu____18603 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____18620 =
                               let uu____18621 =
                                 FStar_Syntax_Subst.compress body in
                               uu____18621.FStar_Syntax_Syntax.n in
                             match uu____18620 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____18680 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____18709 =
                               let uu____18710 =
                                 FStar_Syntax_Subst.compress t in
                               uu____18710.FStar_Syntax_Syntax.n in
                             match uu____18709 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____18731) ->
                                 let uu____18752 = destruct_action_body body in
                                 (match uu____18752 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____18797 ->
                                 let uu____18798 = destruct_action_body t in
                                 (match uu____18798 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____18847 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____18847 with
                           | (action_univs,t) ->
                               let uu____18856 = destruct_action_typ_templ t in
                               (match uu____18856 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___244_18897 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___244_18897.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___244_18897.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___245_18899 = ed in
                           let uu____18900 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____18901 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____18902 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____18903 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____18904 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____18905 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____18906 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____18907 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____18908 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____18909 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____18910 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____18911 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____18912 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____18913 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___245_18899.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___245_18899.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____18900;
                             FStar_Syntax_Syntax.bind_wp = uu____18901;
                             FStar_Syntax_Syntax.if_then_else = uu____18902;
                             FStar_Syntax_Syntax.ite_wp = uu____18903;
                             FStar_Syntax_Syntax.stronger = uu____18904;
                             FStar_Syntax_Syntax.close_wp = uu____18905;
                             FStar_Syntax_Syntax.assert_p = uu____18906;
                             FStar_Syntax_Syntax.assume_p = uu____18907;
                             FStar_Syntax_Syntax.null_wp = uu____18908;
                             FStar_Syntax_Syntax.trivial = uu____18909;
                             FStar_Syntax_Syntax.repr = uu____18910;
                             FStar_Syntax_Syntax.return_repr = uu____18911;
                             FStar_Syntax_Syntax.bind_repr = uu____18912;
                             FStar_Syntax_Syntax.actions = uu____18913
                           } in
                         let uu___246_18916 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___246_18916.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___246_18916.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___246_18916.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___246_18916.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___164_18933 =
            match uu___164_18933 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____18960 = elim_uvars_aux_t env us [] t in
                (match uu____18960 with
                 | (us1,uu____18984,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___247_19003 = sub_eff in
            let uu____19004 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____19007 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___247_19003.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___247_19003.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____19004;
              FStar_Syntax_Syntax.lift = uu____19007
            } in
          let uu___248_19010 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___248_19010.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___248_19010.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___248_19010.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___248_19010.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____19020 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____19020 with
           | (univ_names1,binders1,comp1) ->
               let uu___249_19054 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___249_19054.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___249_19054.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___249_19054.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___249_19054.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____19065 -> s