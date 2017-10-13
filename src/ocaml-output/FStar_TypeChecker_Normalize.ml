open Prims
type step =
  | Beta
  | Iota
  | Zeta
  | Exclude of step
  | Weak
  | HNF
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
let uu___is_Weak: step -> Prims.bool =
  fun projectee  -> match projectee with | Weak  -> true | uu____48 -> false
let uu___is_HNF: step -> Prims.bool =
  fun projectee  -> match projectee with | HNF  -> true | uu____53 -> false
let uu___is_Primops: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____58 -> false
let uu___is_Eager_unfolding: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____63 -> false
let uu___is_Inlining: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____68 -> false
let uu___is_NoDeltaSteps: step -> Prims.bool =
  fun projectee  ->
    match projectee with | NoDeltaSteps  -> true | uu____73 -> false
let uu___is_UnfoldUntil: step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____79 -> false
let __proj__UnfoldUntil__item___0: step -> FStar_Syntax_Syntax.delta_depth =
  fun projectee  -> match projectee with | UnfoldUntil _0 -> _0
let uu___is_UnfoldOnly: step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____95 -> false
let __proj__UnfoldOnly__item___0: step -> FStar_Ident.lid Prims.list =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0
let uu___is_UnfoldTac: step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____114 -> false
let uu___is_PureSubtermsWithinComputations: step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____119 -> false
let uu___is_Simplify: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____124 -> false
let uu___is_EraseUniverses: step -> Prims.bool =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____129 -> false
let uu___is_AllowUnboundUniverses: step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____134 -> false
let uu___is_Reify: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____139 -> false
let uu___is_CompressUvars: step -> Prims.bool =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____144 -> false
let uu___is_NoFullNorm: step -> Prims.bool =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____149 -> false
let uu___is_CheckNoUvars: step -> Prims.bool =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____154 -> false
let uu___is_Unmeta: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____159 -> false
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
    match projectee with | Clos _0 -> true | uu____313 -> false
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
    match projectee with | Univ _0 -> true | uu____381 -> false
let __proj__Univ__item___0: closure -> FStar_Syntax_Syntax.universe =
  fun projectee  -> match projectee with | Univ _0 -> _0
let uu___is_Dummy: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____394 -> false
type env = closure Prims.list[@@deriving show]
let closure_to_string: closure -> Prims.string =
  fun uu___167_400  ->
    match uu___167_400 with
    | Clos (uu____401,t,uu____403,uu____404) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____425 -> "Univ"
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
let only_strong_steps':
  primitive_step Prims.list -> primitive_step Prims.list =
  fun steps  -> FStar_List.filter (fun ps  -> ps.strong_reduction_ok) steps
let only_strong_steps: cfg -> cfg =
  fun cfg  ->
    let uu___183_518 = cfg in
    let uu____519 = only_strong_steps' cfg.primitive_steps in
    {
      steps = (uu___183_518.steps);
      tcenv = (uu___183_518.tcenv);
      delta_level = (uu___183_518.delta_level);
      primitive_steps = uu____519
    }
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
    match projectee with | Arg _0 -> true | uu____666 -> false
let __proj__Arg__item___0:
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Arg _0 -> _0
let uu___is_UnivArgs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____704 -> false
let __proj__UnivArgs__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____742 -> false
let __proj__MemoLazy__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0
let uu___is_Match: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____801 -> false
let __proj__Match__item___0:
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Abs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____845 -> false
let __proj__Abs__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____901 -> false
let __proj__App__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Meta: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____937 -> false
let __proj__Meta__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Meta _0 -> _0
let uu___is_Let: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____971 -> false
let __proj__Let__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Steps: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Steps _0 -> true | uu____1019 -> false
let __proj__Steps__item___0:
  stack_elt ->
    (steps,primitive_step Prims.list,FStar_TypeChecker_Env.delta_level
                                       Prims.list)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Steps _0 -> _0
let uu___is_Debug: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____1067 -> false
let __proj__Debug__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list[@@deriving show]
let mk:
  'Auu____1096 .
    'Auu____1096 ->
      FStar_Range.range -> 'Auu____1096 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r
let set_memo:
  'Auu____1253 'Auu____1254 .
    ('Auu____1254 FStar_Pervasives_Native.option,'Auu____1253) FStar_ST.mref
      -> 'Auu____1254 -> Prims.unit
  =
  fun r  ->
    fun t  ->
      let uu____1549 = FStar_ST.op_Bang r in
      match uu____1549 with
      | FStar_Pervasives_Native.Some uu____1650 ->
          failwith "Unexpected set_memo: thunk already evaluated"
      | FStar_Pervasives_Native.None  ->
          FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____1757 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____1757 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___168_1765  ->
    match uu___168_1765 with
    | Arg (c,uu____1767,uu____1768) ->
        let uu____1769 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____1769
    | MemoLazy uu____1770 -> "MemoLazy"
    | Abs (uu____1777,bs,uu____1779,uu____1780,uu____1781) ->
        let uu____1786 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____1786
    | UnivArgs uu____1791 -> "UnivArgs"
    | Match uu____1798 -> "Match"
    | App (t,uu____1806,uu____1807) ->
        let uu____1808 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____1808
    | Meta (m,uu____1810) -> "Meta"
    | Let uu____1811 -> "Let"
    | Steps (uu____1820,uu____1821,uu____1822) -> "Steps"
    | Debug (t,uu____1832) ->
        let uu____1833 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____1833
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____1842 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____1842 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1860 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____1860 then f () else ()
let log_primops: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1875 =
        (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm"))
          ||
          (FStar_TypeChecker_Env.debug cfg.tcenv
             (FStar_Options.Other "Primops")) in
      if uu____1875 then f () else ()
let is_empty: 'Auu____1881 . 'Auu____1881 Prims.list -> Prims.bool =
  fun uu___169_1887  ->
    match uu___169_1887 with | [] -> true | uu____1890 -> false
let lookup_bvar:
  'Auu____1899 .
    'Auu____1899 Prims.list -> FStar_Syntax_Syntax.bv -> 'Auu____1899
  =
  fun env  ->
    fun x  ->
      try FStar_List.nth env x.FStar_Syntax_Syntax.index
      with
      | uu____1918 ->
          let uu____1919 =
            let uu____1920 = FStar_Syntax_Print.db_to_string x in
            FStar_Util.format1 "Failed to find %s\n" uu____1920 in
          failwith uu____1919
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
          let uu____1965 =
            FStar_List.fold_left
              (fun uu____1991  ->
                 fun u1  ->
                   match uu____1991 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____2016 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____2016 with
                        | (k_u,n1) ->
                            let uu____2031 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____2031
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____1965 with
          | (uu____2049,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____2074 = FStar_List.nth env x in
                 match uu____2074 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____2078 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____2087 ->
                   let uu____2088 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____2088
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____2094 when
              FStar_All.pipe_right cfg.steps
                (FStar_List.contains CheckNoUvars)
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____2103 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____2112 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____2119 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____2119 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____2136 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____2136 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____2144 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____2152 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____2152 with
                                  | (uu____2157,m) -> n1 <= m)) in
                        if uu____2144 then rest1 else us1
                    | uu____2162 -> us1)
               | uu____2167 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____2171 = aux u3 in
              FStar_List.map (fun _0_42  -> FStar_Syntax_Syntax.U_succ _0_42)
                uu____2171 in
        let uu____2174 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____2174
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____2176 = aux u in
           match uu____2176 with
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
          (fun uu____2296  ->
             let uu____2297 = FStar_Syntax_Print.tag_of_term t in
             let uu____2298 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____2297
               uu____2298);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____2299 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____2303 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____2328 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____2329 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____2330 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____2331 ->
                  let uu____2348 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains CheckNoUvars) in
                  if uu____2348
                  then
                    let uu____2349 =
                      let uu____2350 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos in
                      let uu____2351 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____2350 uu____2351 in
                    failwith uu____2349
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____2354 =
                    let uu____2355 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____2355 in
                  mk uu____2354 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____2362 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____2362
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____2364 = lookup_bvar env x in
                  (match uu____2364 with
                   | Univ uu____2365 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____2369) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____2457 = closures_as_binders_delayed cfg env bs in
                  (match uu____2457 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____2491 =
                         let uu____2492 =
                           let uu____2509 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____2509) in
                         FStar_Syntax_Syntax.Tm_abs uu____2492 in
                       mk uu____2491 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____2540 = closures_as_binders_delayed cfg env bs in
                  (match uu____2540 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____2588 =
                    let uu____2601 =
                      let uu____2608 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____2608] in
                    closures_as_binders_delayed cfg env uu____2601 in
                  (match uu____2588 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____2630 =
                         let uu____2631 =
                           let uu____2638 =
                             let uu____2639 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____2639
                               FStar_Pervasives_Native.fst in
                           (uu____2638, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____2631 in
                       mk uu____2630 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____2730 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____2730
                    | FStar_Util.Inr c ->
                        let uu____2744 = close_comp cfg env c in
                        FStar_Util.Inr uu____2744 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____2760 =
                    let uu____2761 =
                      let uu____2788 = closure_as_term_delayed cfg env t11 in
                      (uu____2788, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____2761 in
                  mk uu____2760 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____2839 =
                    let uu____2840 =
                      let uu____2847 = closure_as_term_delayed cfg env t' in
                      let uu____2850 =
                        let uu____2851 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____2851 in
                      (uu____2847, uu____2850) in
                    FStar_Syntax_Syntax.Tm_meta uu____2840 in
                  mk uu____2839 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____2911 =
                    let uu____2912 =
                      let uu____2919 = closure_as_term_delayed cfg env t' in
                      let uu____2922 =
                        let uu____2923 =
                          let uu____2930 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____2930) in
                        FStar_Syntax_Syntax.Meta_monadic uu____2923 in
                      (uu____2919, uu____2922) in
                    FStar_Syntax_Syntax.Tm_meta uu____2912 in
                  mk uu____2911 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____2949 =
                    let uu____2950 =
                      let uu____2957 = closure_as_term_delayed cfg env t' in
                      let uu____2960 =
                        let uu____2961 =
                          let uu____2970 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____2970) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____2961 in
                      (uu____2957, uu____2960) in
                    FStar_Syntax_Syntax.Tm_meta uu____2950 in
                  mk uu____2949 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____2983 =
                    let uu____2984 =
                      let uu____2991 = closure_as_term_delayed cfg env t' in
                      (uu____2991, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____2984 in
                  mk uu____2983 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____3021  -> Dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let uu____3028 =
                    let uu____3039 = FStar_Syntax_Syntax.is_top_level [lb] in
                    if uu____3039
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       let uu____3058 =
                         closure_as_term cfg (Dummy :: env0) body in
                       ((FStar_Util.Inl
                           (let uu___188_3064 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___188_3064.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___188_3064.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____3058)) in
                  (match uu____3028 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___189_3080 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___189_3080.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___189_3080.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         } in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____3091,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____3126  -> fun env2  -> Dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____3133 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____3133
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____3141  -> fun env2  -> Dummy :: env2) lbs
                          env_univs in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let nm =
                      let uu____3151 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____3151
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         FStar_All.pipe_right
                           (let uu___190_3163 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___190_3163.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___190_3163.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_43  -> FStar_Util.Inl _0_43)) in
                    let uu___191_3164 = lb in
                    let uu____3165 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___191_3164.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___191_3164.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____3165
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____3183  -> fun env1  -> Dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____3262 =
                    match uu____3262 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____3327 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____3350 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____3416  ->
                                        fun uu____3417  ->
                                          match (uu____3416, uu____3417) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____3520 =
                                                norm_pat env3 p1 in
                                              (match uu____3520 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____3350 with
                               | (pats1,env3) ->
                                   ((let uu___192_3622 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___192_3622.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___193_3641 = x in
                                let uu____3642 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___193_3641.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___193_3641.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3642
                                } in
                              ((let uu___194_3650 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___194_3650.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___195_3655 = x in
                                let uu____3656 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___195_3655.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___195_3655.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3656
                                } in
                              ((let uu___196_3664 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___196_3664.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___197_3674 = x in
                                let uu____3675 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___197_3674.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___197_3674.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3675
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___198_3684 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___198_3684.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____3687 = norm_pat env1 pat in
                        (match uu____3687 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3722 =
                                     closure_as_term cfg env2 w in
                                   FStar_Pervasives_Native.Some uu____3722 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____3728 =
                    let uu____3729 =
                      let uu____3752 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____3752) in
                    FStar_Syntax_Syntax.Tm_match uu____3729 in
                  mk uu____3728 t1.FStar_Syntax_Syntax.pos))
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
        | uu____3834 -> closure_as_term cfg env t
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
        | uu____3858 ->
            FStar_List.map
              (fun uu____3877  ->
                 match uu____3877 with
                 | (x,imp) ->
                     let uu____3896 = closure_as_term_delayed cfg env x in
                     (uu____3896, imp)) args
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
        let uu____3912 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____3967  ->
                  fun uu____3968  ->
                    match (uu____3967, uu____3968) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___199_4050 = b in
                          let uu____4051 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___199_4050.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___199_4050.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____4051
                          } in
                        let env2 = Dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____3912 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____4132 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____4147 = closure_as_term_delayed cfg env t in
                 let uu____4148 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____4147 uu____4148
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____4161 = closure_as_term_delayed cfg env t in
                 let uu____4162 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____4161 uu____4162
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
                        (fun uu___170_4188  ->
                           match uu___170_4188 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____4192 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____4192
                           | f -> f)) in
                 let uu____4196 =
                   let uu___200_4197 = c1 in
                   let uu____4198 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____4198;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___200_4197.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____4196)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags  ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___171_4208  ->
            match uu___171_4208 with
            | FStar_Syntax_Syntax.DECREASES uu____4209 -> false
            | uu____4212 -> true))
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
                   (fun uu___172_4232  ->
                      match uu___172_4232 with
                      | FStar_Syntax_Syntax.DECREASES uu____4233 -> false
                      | uu____4236 -> true)) in
            let rc1 =
              let uu___201_4238 = rc in
              let uu____4239 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___201_4238.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____4239;
                FStar_Syntax_Syntax.residual_flags = flags
              } in
            FStar_Pervasives_Native.Some rc1
        | uu____4246 -> lopt
let built_in_primitive_steps: primitive_step Prims.list =
  let arg_as_int a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_int_safe in
  let arg_as_bool a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_bool_safe in
  let arg_as_char a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_char_safe in
  let arg_as_string a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_string_safe in
  let arg_as_list u a =
    let uu____4334 = FStar_Syntax_Embeddings.unembed_list_safe u in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____4334 in
  let arg_as_bounded_int uu____4362 =
    match uu____4362 with
    | (a,uu____4374) ->
        let uu____4381 =
          let uu____4382 = FStar_Syntax_Subst.compress a in
          uu____4382.FStar_Syntax_Syntax.n in
        (match uu____4381 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____4392;
                FStar_Syntax_Syntax.vars = uu____4393;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____4395;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____4396;_},uu____4397)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____4436 =
               let uu____4441 = FStar_Util.int_of_string i in
               (fv1, uu____4441) in
             FStar_Pervasives_Native.Some uu____4436
         | uu____4446 -> FStar_Pervasives_Native.None) in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4488 = f a in FStar_Pervasives_Native.Some uu____4488
    | uu____4489 -> FStar_Pervasives_Native.None in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4539 = f a0 a1 in FStar_Pervasives_Native.Some uu____4539
    | uu____4540 -> FStar_Pervasives_Native.None in
  let unary_op as_a f r args =
    let uu____4589 = FStar_List.map as_a args in lift_unary (f r) uu____4589 in
  let binary_op as_a f r args =
    let uu____4645 = FStar_List.map as_a args in lift_binary (f r) uu____4645 in
  let as_primitive_step uu____4669 =
    match uu____4669 with
    | (l,arity,f) ->
        { name = l; arity; strong_reduction_ok = true; interpretation = f } in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  ->
         fun x  ->
           let uu____4717 = f x in
           FStar_Syntax_Embeddings.embed_int r uu____4717) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4745 = f x y in
             FStar_Syntax_Embeddings.embed_int r uu____4745) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____4766 = f x in
           FStar_Syntax_Embeddings.embed_bool r uu____4766) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4794 = f x y in
             FStar_Syntax_Embeddings.embed_bool r uu____4794) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4822 = f x y in
             FStar_Syntax_Embeddings.embed_string r uu____4822) in
  let list_of_string' rng s =
    let name l =
      let uu____4836 =
        let uu____4837 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____4837 in
      mk uu____4836 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____4847 =
      let uu____4850 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____4850 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____4847 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in
    FStar_Syntax_Embeddings.embed_int rng r in
  let string_concat' rng args =
    match args with
    | a1::a2::[] ->
        let uu____4897 = arg_as_string a1 in
        (match uu____4897 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4903 =
               arg_as_list FStar_Syntax_Embeddings.unembed_string_safe a2 in
             (match uu____4903 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____4916 = FStar_Syntax_Embeddings.embed_string rng r in
                  FStar_Pervasives_Native.Some uu____4916
              | uu____4917 -> FStar_Pervasives_Native.None)
         | uu____4922 -> FStar_Pervasives_Native.None)
    | uu____4925 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____4935 = FStar_Util.string_of_int i in
    FStar_Syntax_Embeddings.embed_string rng uu____4935 in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____4951 = FStar_Util.string_of_int i in
    FStar_Syntax_Embeddings.embed_string rng uu____4951 in
  let string_of_bool2 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false") in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r in
  let range_of1 uu____4981 args =
    match args with
    | uu____4993::(t,uu____4995)::[] ->
        let uu____5024 = term_of_range t.FStar_Syntax_Syntax.pos in
        FStar_Pervasives_Native.Some uu____5024
    | uu____5029 -> FStar_Pervasives_Native.None in
  let set_range_of1 r args =
    match args with
    | uu____5061::(t,uu____5063)::(r1,uu____5065)::[] ->
        let uu____5086 = FStar_Syntax_Embeddings.unembed_range_safe r1 in
        FStar_Util.bind_opt uu____5086
          (fun r2  ->
             FStar_Pervasives_Native.Some
               (let uu___202_5096 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___202_5096.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r2;
                  FStar_Syntax_Syntax.vars =
                    (uu___202_5096.FStar_Syntax_Syntax.vars)
                }))
    | uu____5097 -> FStar_Pervasives_Native.None in
  let mk_range1 r args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____5124 =
          let uu____5145 = arg_as_string fn in
          let uu____5148 = arg_as_int from_line in
          let uu____5151 = arg_as_int from_col in
          let uu____5154 = arg_as_int to_line in
          let uu____5157 = arg_as_int to_col in
          (uu____5145, uu____5148, uu____5151, uu____5154, uu____5157) in
        (match uu____5124 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r1 =
               let uu____5188 = FStar_Range.mk_pos from_l from_c in
               let uu____5189 = FStar_Range.mk_pos to_l to_c in
               FStar_Range.mk_range fn1 uu____5188 uu____5189 in
             let uu____5190 = term_of_range r1 in
             FStar_Pervasives_Native.Some uu____5190
         | uu____5195 -> FStar_Pervasives_Native.None)
    | uu____5216 -> FStar_Pervasives_Native.None in
  let decidable_eq neg rng args =
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) rng in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) rng in
    match args with
    | (_typ,uu____5242)::(a1,uu____5244)::(a2,uu____5246)::[] ->
        let uu____5283 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____5283 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____5296 -> FStar_Pervasives_Native.None)
    | uu____5297 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____5315 =
      let uu____5330 =
        let uu____5345 =
          let uu____5360 =
            let uu____5375 =
              let uu____5390 =
                let uu____5405 =
                  let uu____5420 =
                    let uu____5435 =
                      let uu____5450 =
                        let uu____5465 =
                          let uu____5480 =
                            let uu____5495 =
                              let uu____5510 =
                                let uu____5525 =
                                  let uu____5540 =
                                    let uu____5555 =
                                      let uu____5570 =
                                        let uu____5585 =
                                          let uu____5600 =
                                            let uu____5615 =
                                              let uu____5628 =
                                                FStar_Parser_Const.p2l
                                                  ["FStar";
                                                  "String";
                                                  "list_of_string"] in
                                              (uu____5628,
                                                (Prims.parse_int "1"),
                                                (unary_op arg_as_string
                                                   list_of_string')) in
                                            let uu____5635 =
                                              let uu____5650 =
                                                let uu____5663 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "string_of_list"] in
                                                (uu____5663,
                                                  (Prims.parse_int "1"),
                                                  (unary_op
                                                     (arg_as_list
                                                        FStar_Syntax_Embeddings.unembed_char_safe)
                                                     string_of_list')) in
                                              let uu____5672 =
                                                let uu____5687 =
                                                  let uu____5702 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "concat"] in
                                                  (uu____5702,
                                                    (Prims.parse_int "2"),
                                                    string_concat') in
                                                let uu____5711 =
                                                  let uu____5728 =
                                                    let uu____5749 =
                                                      FStar_Parser_Const.p2l
                                                        ["Prims"; "range_of"] in
                                                    (uu____5749,
                                                      (Prims.parse_int "2"),
                                                      range_of1) in
                                                  let uu____5764 =
                                                    let uu____5787 =
                                                      let uu____5806 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "set_range_of"] in
                                                      (uu____5806,
                                                        (Prims.parse_int "3"),
                                                        set_range_of1) in
                                                    let uu____5819 =
                                                      let uu____5840 =
                                                        let uu____5855 =
                                                          FStar_Parser_Const.p2l
                                                            ["Prims";
                                                            "mk_range"] in
                                                        (uu____5855,
                                                          (Prims.parse_int
                                                             "5"), mk_range1) in
                                                      [uu____5840] in
                                                    uu____5787 :: uu____5819 in
                                                  uu____5728 :: uu____5764 in
                                                uu____5687 :: uu____5711 in
                                              uu____5650 :: uu____5672 in
                                            uu____5615 :: uu____5635 in
                                          (FStar_Parser_Const.op_notEq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq true)) ::
                                            uu____5600 in
                                        (FStar_Parser_Const.op_Eq,
                                          (Prims.parse_int "3"),
                                          (decidable_eq false)) :: uu____5585 in
                                      (FStar_Parser_Const.string_compare,
                                        (Prims.parse_int "2"),
                                        (binary_op arg_as_string
                                           string_compare'))
                                        :: uu____5570 in
                                    (FStar_Parser_Const.string_of_bool_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_bool string_of_bool2))
                                      :: uu____5555 in
                                  (FStar_Parser_Const.string_of_int_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_int string_of_int2)) ::
                                    uu____5540 in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____5525 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5510 in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____5495 in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____5480 in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____5465 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____5450 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                FStar_Syntax_Embeddings.embed_bool r (x >= y))))
                      :: uu____5435 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              FStar_Syntax_Embeddings.embed_bool r (x > y))))
                    :: uu____5420 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            FStar_Syntax_Embeddings.embed_bool r (x <= y))))
                  :: uu____5405 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          FStar_Syntax_Embeddings.embed_bool r (x < y))))
                :: uu____5390 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____5375 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____5360 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____5345 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____5330 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____5315 in
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
      let c = FStar_Syntax_Embeddings.embed_int r n1 in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1 in
      let uu____6444 =
        let uu____6445 =
          let uu____6446 = FStar_Syntax_Syntax.as_arg c in [uu____6446] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6445 in
      uu____6444 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____6481 =
              let uu____6494 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____6494, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____6513  ->
                        fun uu____6514  ->
                          match (uu____6513, uu____6514) with
                          | ((int_to_t1,x),(uu____6533,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____6543 =
              let uu____6558 =
                let uu____6571 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____6571, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____6590  ->
                          fun uu____6591  ->
                            match (uu____6590, uu____6591) with
                            | ((int_to_t1,x),(uu____6610,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____6620 =
                let uu____6635 =
                  let uu____6648 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____6648, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____6667  ->
                            fun uu____6668  ->
                              match (uu____6667, uu____6668) with
                              | ((int_to_t1,x),(uu____6687,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____6635] in
              uu____6558 :: uu____6620 in
            uu____6481 :: uu____6543)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop r args =
    match args with
    | (_typ,uu____6783)::(a1,uu____6785)::(a2,uu____6787)::[] ->
        let uu____6824 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6824 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___203_6830 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___203_6830.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___203_6830.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___204_6834 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___204_6834.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___204_6834.FStar_Syntax_Syntax.vars)
                })
         | uu____6835 -> FStar_Pervasives_Native.None)
    | (_typ,uu____6837)::uu____6838::(a1,uu____6840)::(a2,uu____6842)::[] ->
        let uu____6891 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6891 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___203_6897 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___203_6897.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___203_6897.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___204_6901 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___204_6901.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___204_6901.FStar_Syntax_Syntax.vars)
                })
         | uu____6902 -> FStar_Pervasives_Native.None)
    | uu____6903 -> failwith "Unexpected number of arguments" in
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
      let uu____6916 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops cfg.steps) in
      if uu____6916
      then tm
      else
        (let uu____6918 = FStar_Syntax_Util.head_and_args tm in
         match uu____6918 with
         | (head1,args) ->
             let uu____6955 =
               let uu____6956 = FStar_Syntax_Util.un_uinst head1 in
               uu____6956.FStar_Syntax_Syntax.n in
             (match uu____6955 with
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____6960 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps in
                  (match uu____6960 with
                   | FStar_Pervasives_Native.None  -> tm
                   | FStar_Pervasives_Native.Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then
                         (log_primops cfg
                            (fun uu____6977  ->
                               let uu____6978 =
                                 FStar_Syntax_Print.lid_to_string
                                   prim_step.name in
                               let uu____6979 =
                                 FStar_Util.string_of_int
                                   (FStar_List.length args) in
                               let uu____6986 =
                                 FStar_Util.string_of_int prim_step.arity in
                               FStar_Util.print3
                                 "primop: found partially applied %s (%s/%s args)\n"
                                 uu____6978 uu____6979 uu____6986);
                          tm)
                       else
                         (log_primops cfg
                            (fun uu____6991  ->
                               let uu____6992 =
                                 FStar_Syntax_Print.term_to_string tm in
                               FStar_Util.print1
                                 "primop: trying to reduce <%s>\n" uu____6992);
                          (let uu____6993 =
                             prim_step.interpretation
                               head1.FStar_Syntax_Syntax.pos args in
                           match uu____6993 with
                           | FStar_Pervasives_Native.None  ->
                               (log_primops cfg
                                  (fun uu____6999  ->
                                     let uu____7000 =
                                       FStar_Syntax_Print.term_to_string tm in
                                     FStar_Util.print1
                                       "primop: <%s> did not reduce\n"
                                       uu____7000);
                                tm)
                           | FStar_Pervasives_Native.Some reduced ->
                               (log_primops cfg
                                  (fun uu____7006  ->
                                     let uu____7007 =
                                       FStar_Syntax_Print.term_to_string tm in
                                     let uu____7008 =
                                       FStar_Syntax_Print.term_to_string
                                         reduced in
                                     FStar_Util.print2
                                       "primop: <%s> reduced to <%s>\n"
                                       uu____7007 uu____7008);
                                reduced))))
              | uu____7009 -> tm))
let reduce_equality:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___205_7020 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___205_7020.tcenv);
           delta_level = (uu___205_7020.delta_level);
           primitive_steps = equality_ops
         }) tm
let maybe_simplify:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      let tm1 = reduce_primops cfg tm in
      let uu____7030 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify cfg.steps) in
      if uu____7030
      then tm1
      else
        (let w t =
           let uu___206_7042 = t in
           {
             FStar_Syntax_Syntax.n = (uu___206_7042.FStar_Syntax_Syntax.n);
             FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
             FStar_Syntax_Syntax.vars =
               (uu___206_7042.FStar_Syntax_Syntax.vars)
           } in
         let simp_t t =
           match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
               -> FStar_Pervasives_Native.Some true
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
               -> FStar_Pervasives_Native.Some false
           | uu____7059 -> FStar_Pervasives_Native.None in
         let simplify1 arg =
           ((simp_t (FStar_Pervasives_Native.fst arg)), arg) in
         match tm1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.pos = uu____7099;
                     FStar_Syntax_Syntax.vars = uu____7100;_},uu____7101);
                FStar_Syntax_Syntax.pos = uu____7102;
                FStar_Syntax_Syntax.vars = uu____7103;_},args)
             ->
             let uu____7129 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
             if uu____7129
             then
               let uu____7130 =
                 FStar_All.pipe_right args (FStar_List.map simplify1) in
               (match uu____7130 with
                | (FStar_Pervasives_Native.Some (true ),uu____7185)::
                    (uu____7186,(arg,uu____7188))::[] -> arg
                | (uu____7253,(arg,uu____7255))::(FStar_Pervasives_Native.Some
                                                  (true ),uu____7256)::[]
                    -> arg
                | (FStar_Pervasives_Native.Some (false ),uu____7321)::uu____7322::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____7385::(FStar_Pervasives_Native.Some (false
                               ),uu____7386)::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____7449 -> tm1)
             else
               (let uu____7465 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
                if uu____7465
                then
                  let uu____7466 =
                    FStar_All.pipe_right args (FStar_List.map simplify1) in
                  match uu____7466 with
                  | (FStar_Pervasives_Native.Some (true ),uu____7521)::uu____7522::[]
                      -> w FStar_Syntax_Util.t_true
                  | uu____7585::(FStar_Pervasives_Native.Some (true
                                 ),uu____7586)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____7649)::
                      (uu____7650,(arg,uu____7652))::[] -> arg
                  | (uu____7717,(arg,uu____7719))::(FStar_Pervasives_Native.Some
                                                    (false ),uu____7720)::[]
                      -> arg
                  | uu____7785 -> tm1
                else
                  (let uu____7801 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.imp_lid in
                   if uu____7801
                   then
                     let uu____7802 =
                       FStar_All.pipe_right args (FStar_List.map simplify1) in
                     match uu____7802 with
                     | uu____7857::(FStar_Pervasives_Native.Some (true
                                    ),uu____7858)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____7921)::uu____7922::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____7985)::
                         (uu____7986,(arg,uu____7988))::[] -> arg
                     | (uu____8053,(p,uu____8055))::(uu____8056,(q,uu____8058))::[]
                         ->
                         let uu____8123 = FStar_Syntax_Util.term_eq p q in
                         (if uu____8123
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____8125 -> tm1
                   else
                     (let uu____8141 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____8141
                      then
                        let uu____8142 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1) in
                        match uu____8142 with
                        | (FStar_Pervasives_Native.Some (true ),uu____8197)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____8236)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____8275 -> tm1
                      else
                        (let uu____8291 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____8291
                         then
                           match args with
                           | (t,uu____8293)::[] ->
                               let uu____8310 =
                                 let uu____8311 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____8311.FStar_Syntax_Syntax.n in
                               (match uu____8310 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____8314::[],body,uu____8316) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____8343 -> tm1)
                                | uu____8346 -> tm1)
                           | (uu____8347,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____8348))::
                               (t,uu____8350)::[] ->
                               let uu____8389 =
                                 let uu____8390 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____8390.FStar_Syntax_Syntax.n in
                               (match uu____8389 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____8393::[],body,uu____8395) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____8422 -> tm1)
                                | uu____8425 -> tm1)
                           | uu____8426 -> tm1
                         else
                           (let uu____8436 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____8436
                            then
                              match args with
                              | (t,uu____8438)::[] ->
                                  let uu____8455 =
                                    let uu____8456 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____8456.FStar_Syntax_Syntax.n in
                                  (match uu____8455 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____8459::[],body,uu____8461) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____8488 -> tm1)
                                   | uu____8491 -> tm1)
                              | (uu____8492,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____8493))::
                                  (t,uu____8495)::[] ->
                                  let uu____8534 =
                                    let uu____8535 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____8535.FStar_Syntax_Syntax.n in
                                  (match uu____8534 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____8538::[],body,uu____8540) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____8567 -> tm1)
                                   | uu____8570 -> tm1)
                              | uu____8571 -> tm1
                            else reduce_equality cfg tm1)))))
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                FStar_Syntax_Syntax.pos = uu____8582;
                FStar_Syntax_Syntax.vars = uu____8583;_},args)
             ->
             let uu____8605 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
             if uu____8605
             then
               let uu____8606 =
                 FStar_All.pipe_right args (FStar_List.map simplify1) in
               (match uu____8606 with
                | (FStar_Pervasives_Native.Some (true ),uu____8661)::
                    (uu____8662,(arg,uu____8664))::[] -> arg
                | (uu____8729,(arg,uu____8731))::(FStar_Pervasives_Native.Some
                                                  (true ),uu____8732)::[]
                    -> arg
                | (FStar_Pervasives_Native.Some (false ),uu____8797)::uu____8798::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____8861::(FStar_Pervasives_Native.Some (false
                               ),uu____8862)::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____8925 -> tm1)
             else
               (let uu____8941 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
                if uu____8941
                then
                  let uu____8942 =
                    FStar_All.pipe_right args (FStar_List.map simplify1) in
                  match uu____8942 with
                  | (FStar_Pervasives_Native.Some (true ),uu____8997)::uu____8998::[]
                      -> w FStar_Syntax_Util.t_true
                  | uu____9061::(FStar_Pervasives_Native.Some (true
                                 ),uu____9062)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____9125)::
                      (uu____9126,(arg,uu____9128))::[] -> arg
                  | (uu____9193,(arg,uu____9195))::(FStar_Pervasives_Native.Some
                                                    (false ),uu____9196)::[]
                      -> arg
                  | uu____9261 -> tm1
                else
                  (let uu____9277 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.imp_lid in
                   if uu____9277
                   then
                     let uu____9278 =
                       FStar_All.pipe_right args (FStar_List.map simplify1) in
                     match uu____9278 with
                     | uu____9333::(FStar_Pervasives_Native.Some (true
                                    ),uu____9334)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____9397)::uu____9398::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____9461)::
                         (uu____9462,(arg,uu____9464))::[] -> arg
                     | (uu____9529,(p,uu____9531))::(uu____9532,(q,uu____9534))::[]
                         ->
                         let uu____9599 = FStar_Syntax_Util.term_eq p q in
                         (if uu____9599
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____9601 -> tm1
                   else
                     (let uu____9617 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____9617
                      then
                        let uu____9618 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1) in
                        match uu____9618 with
                        | (FStar_Pervasives_Native.Some (true ),uu____9673)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____9712)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____9751 -> tm1
                      else
                        (let uu____9767 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____9767
                         then
                           match args with
                           | (t,uu____9769)::[] ->
                               let uu____9786 =
                                 let uu____9787 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____9787.FStar_Syntax_Syntax.n in
                               (match uu____9786 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____9790::[],body,uu____9792) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____9819 -> tm1)
                                | uu____9822 -> tm1)
                           | (uu____9823,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____9824))::
                               (t,uu____9826)::[] ->
                               let uu____9865 =
                                 let uu____9866 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____9866.FStar_Syntax_Syntax.n in
                               (match uu____9865 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____9869::[],body,uu____9871) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____9898 -> tm1)
                                | uu____9901 -> tm1)
                           | uu____9902 -> tm1
                         else
                           (let uu____9912 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____9912
                            then
                              match args with
                              | (t,uu____9914)::[] ->
                                  let uu____9931 =
                                    let uu____9932 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____9932.FStar_Syntax_Syntax.n in
                                  (match uu____9931 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____9935::[],body,uu____9937) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____9964 -> tm1)
                                   | uu____9967 -> tm1)
                              | (uu____9968,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____9969))::
                                  (t,uu____9971)::[] ->
                                  let uu____10010 =
                                    let uu____10011 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____10011.FStar_Syntax_Syntax.n in
                                  (match uu____10010 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____10014::[],body,uu____10016) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____10043 -> tm1)
                                   | uu____10046 -> tm1)
                              | uu____10047 -> tm1
                            else reduce_equality cfg tm1)))))
         | uu____10057 -> tm1)
let is_norm_request:
  'Auu____10064 .
    FStar_Syntax_Syntax.term -> 'Auu____10064 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10077 =
        let uu____10084 =
          let uu____10085 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10085.FStar_Syntax_Syntax.n in
        (uu____10084, args) in
      match uu____10077 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10091::uu____10092::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10096::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10101::uu____10102::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10105 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___173_10117  ->
    match uu___173_10117 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10123 =
          let uu____10126 =
            let uu____10127 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____10127 in
          [uu____10126] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10123
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____10146 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10146) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10184 =
          let uu____10187 =
            let uu____10192 =
              FStar_Syntax_Embeddings.unembed_list
                FStar_Syntax_Embeddings.unembed_norm_step in
            uu____10192 s in
          FStar_All.pipe_right uu____10187 FStar_Util.must in
        FStar_All.pipe_right uu____10184 tr_norm_steps in
      match args with
      | uu____10217::(tm,uu____10219)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____10242)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____10257)::uu____10258::(tm,uu____10260)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____10300 =
              let uu____10303 = full_norm steps in parse_steps uu____10303 in
            Beta :: uu____10300 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____10312 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___174_10330  ->
    match uu___174_10330 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.pos = uu____10333;
           FStar_Syntax_Syntax.vars = uu____10334;_},uu____10335,uu____10336))::uu____10337
        -> true
    | uu____10344 -> false
let should_reify: cfg -> stack_elt Prims.list -> Prims.bool =
  fun cfg  ->
    fun stack1  ->
      match stack1 with
      | (App
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify );
             FStar_Syntax_Syntax.pos = uu____10359;
             FStar_Syntax_Syntax.vars = uu____10360;_},uu____10361,uu____10362))::uu____10363
          -> FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)
      | uu____10370 -> false
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
            (fun uu____10517  ->
               let uu____10518 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____10519 = FStar_Syntax_Print.term_to_string t1 in
               let uu____10520 =
                 let uu____10521 =
                   let uu____10524 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____10524 in
                 stack_to_string uu____10521 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____10518
                 uu____10519 uu____10520);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____10547 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____10572 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____10589 =
                 let uu____10590 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____10591 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____10590 uu____10591 in
               failwith uu____10589
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____10592 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____10609 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____10610 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10611;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____10612;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10615;
                 FStar_Syntax_Syntax.fv_delta = uu____10616;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10617;
                 FStar_Syntax_Syntax.fv_delta = uu____10618;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____10619);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar fv when
               let uu____10627 = FStar_Syntax_Syntax.lid_of_fv fv in
               FStar_TypeChecker_Env.is_action cfg.tcenv uu____10627 ->
               let b = should_reify cfg stack1 in
               (log cfg
                  (fun uu____10633  ->
                     let uu____10634 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____10635 = FStar_Util.string_of_bool b in
                     FStar_Util.print2
                       ">>> For DM4F action %s, should_reify = %s\n"
                       uu____10634 uu____10635);
                if b
                then
                  (let uu____10636 = FStar_List.tl stack1 in
                   do_unfold_fv cfg env uu____10636 t1 fv)
                else rebuild cfg env stack1 t1)
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((FStar_Syntax_Util.is_fstar_tactics_embed hd1) ||
                  ((FStar_Syntax_Util.is_fstar_tactics_quote hd1) &&
                     (FStar_List.contains NoDeltaSteps cfg.steps)))
                 || (FStar_Syntax_Util.is_fstar_tactics_by_tactic hd1)
               ->
               let args1 = closures_as_args_delayed cfg env args in
               let hd2 = closure_as_term cfg env hd1 in
               let t2 =
                 let uu___207_10675 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___207_10675.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___207_10675.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____10708 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____10708) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___208_10716 = cfg in
                 let uu____10717 =
                   FStar_List.filter
                     (fun uu___175_10720  ->
                        match uu___175_10720 with
                        | UnfoldOnly uu____10721 -> false
                        | NoDeltaSteps  -> false
                        | uu____10724 -> true) cfg.steps in
                 {
                   steps = uu____10717;
                   tcenv = (uu___208_10716.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___208_10716.primitive_steps)
                 } in
               let uu____10725 = get_norm_request (norm cfg' env []) args in
               (match uu____10725 with
                | (s,tm) ->
                    let delta_level =
                      let uu____10741 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___176_10746  ->
                                match uu___176_10746 with
                                | UnfoldUntil uu____10747 -> true
                                | UnfoldOnly uu____10748 -> true
                                | uu____10751 -> false)) in
                      if uu____10741
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___209_10756 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___209_10756.tcenv);
                        delta_level;
                        primitive_steps = (uu___209_10756.primitive_steps)
                      } in
                    let stack' =
                      let tail1 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let uu____10767 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____10767
                      then
                        let uu____10770 =
                          let uu____10771 =
                            let uu____10776 = FStar_Util.now () in
                            (t1, uu____10776) in
                          Debug uu____10771 in
                        uu____10770 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____10778;
                  FStar_Syntax_Syntax.vars = uu____10779;_},a1::a2::rest)
               ->
               let uu____10827 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____10827 with
                | (hd1,uu____10843) ->
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
                    (FStar_Const.Const_reflect uu____10908);
                  FStar_Syntax_Syntax.pos = uu____10909;
                  FStar_Syntax_Syntax.vars = uu____10910;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____10942 = FStar_List.tl stack1 in
               norm cfg env uu____10942 (FStar_Pervasives_Native.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____10945;
                  FStar_Syntax_Syntax.vars = uu____10946;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____10978 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____10978 with
                | (reify_head,uu____10994) ->
                    let a1 =
                      let uu____11016 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (FStar_Pervasives_Native.fst a) in
                      FStar_Syntax_Subst.compress uu____11016 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____11019);
                            FStar_Syntax_Syntax.pos = uu____11020;
                            FStar_Syntax_Syntax.vars = uu____11021;_},a2::[])
                         ->
                         norm cfg env stack1 (FStar_Pervasives_Native.fst a2)
                     | uu____11055 ->
                         let stack2 =
                           (App
                              (reify_head, FStar_Pervasives_Native.None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11065 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____11065
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11072 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11072
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____11075 =
                      let uu____11082 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11082, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11075 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___177_11095  ->
                         match uu___177_11095 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11098 =
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
                 if uu____11098
                 then false
                 else
                   (let uu____11100 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___178_11107  ->
                              match uu___178_11107 with
                              | UnfoldOnly uu____11108 -> true
                              | uu____11111 -> false)) in
                    match uu____11100 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11115 -> should_delta) in
               (log cfg
                  (fun uu____11123  ->
                     let uu____11124 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11125 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____11126 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11124 uu____11125 uu____11126);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack1 t1
                else do_unfold_fv cfg env stack1 t1 f)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11129 = lookup_bvar env x in
               (match uu____11129 with
                | Univ uu____11130 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11155 = FStar_ST.op_Bang r in
                      (match uu____11155 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11256  ->
                                 let uu____11257 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____11258 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11257
                                   uu____11258);
                            (let uu____11259 =
                               let uu____11260 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____11260.FStar_Syntax_Syntax.n in
                             match uu____11259 with
                             | FStar_Syntax_Syntax.Tm_abs uu____11263 ->
                                 norm cfg env2 stack1 t'
                             | uu____11280 -> rebuild cfg env2 stack1 t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____11332)::uu____11333 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11342)::uu____11343 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11353,uu____11354))::stack_rest ->
                    (match c with
                     | Univ uu____11358 -> norm cfg (c :: env) stack_rest t1
                     | uu____11359 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____11364::[] ->
                              (log cfg
                                 (fun uu____11380  ->
                                    let uu____11381 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11381);
                               norm cfg (c :: env) stack_rest body)
                          | uu____11382::tl1 ->
                              (log cfg
                                 (fun uu____11401  ->
                                    let uu____11402 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11402);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___210_11432 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___210_11432.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____11517  ->
                          let uu____11518 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11518);
                     norm cfg env stack2 t1)
                | (Debug uu____11519)::uu____11520 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____11527 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11527
                    else
                      (let uu____11529 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11529 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11553  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11569 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11569
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11579 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11579)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___211_11584 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___211_11584.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___211_11584.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11585 -> lopt in
                           (log cfg
                              (fun uu____11591  ->
                                 let uu____11592 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11592);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 = only_strong_steps cfg in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____11609)::uu____11610 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____11617 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11617
                    else
                      (let uu____11619 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11619 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11643  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11659 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11659
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11669 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11669)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___211_11674 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___211_11674.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___211_11674.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11675 -> lopt in
                           (log cfg
                              (fun uu____11681  ->
                                 let uu____11682 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11682);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 = only_strong_steps cfg in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____11699)::uu____11700 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____11711 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11711
                    else
                      (let uu____11713 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11713 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11737  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11753 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11753
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11763 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11763)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___211_11768 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___211_11768.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___211_11768.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11769 -> lopt in
                           (log cfg
                              (fun uu____11775  ->
                                 let uu____11776 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11776);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 = only_strong_steps cfg in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____11793)::uu____11794 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____11803 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11803
                    else
                      (let uu____11805 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11805 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11829  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11845 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11845
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11855 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11855)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___211_11860 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___211_11860.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___211_11860.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11861 -> lopt in
                           (log cfg
                              (fun uu____11867  ->
                                 let uu____11868 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11868);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 = only_strong_steps cfg in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____11885)::uu____11886 ->
                    if FStar_List.contains Weak cfg.steps
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
                                   (let uu___211_11958 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___211_11958.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___211_11958.FStar_Syntax_Syntax.residual_flags)
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
                             let cfg1 = only_strong_steps cfg in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____11983 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11983
                    else
                      (let uu____11985 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11985 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12009  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12025 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12025
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12035 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12035)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___211_12040 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___211_12040.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___211_12040.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12041 -> lopt in
                           (log cfg
                              (fun uu____12047  ->
                                 let uu____12048 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12048);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 = only_strong_steps cfg in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1))))
           | FStar_Syntax_Syntax.Tm_app (head1,args) ->
               let stack2 =
                 FStar_All.pipe_right stack1
                   (FStar_List.fold_right
                      (fun uu____12103  ->
                         fun stack2  ->
                           match uu____12103 with
                           | (a,aq) ->
                               let uu____12115 =
                                 let uu____12116 =
                                   let uu____12123 =
                                     let uu____12124 =
                                       let uu____12143 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____12143, false) in
                                     Clos uu____12124 in
                                   (uu____12123, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____12116 in
                               uu____12115 :: stack2) args) in
               (log cfg
                  (fun uu____12195  ->
                     let uu____12196 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12196);
                norm cfg env stack2 head1)
           | FStar_Syntax_Syntax.Tm_refine (x,f) ->
               if FStar_List.contains Weak cfg.steps
               then
                 (match (env, stack1) with
                  | ([],[]) ->
                      let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                      let t2 =
                        mk
                          (FStar_Syntax_Syntax.Tm_refine
                             ((let uu___212_12220 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___212_12220.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___212_12220.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____12221 ->
                      let uu____12226 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12226)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____12229 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____12229 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____12254 =
                          let uu____12255 =
                            let uu____12262 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___213_12264 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___213_12264.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___213_12264.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12262) in
                          FStar_Syntax_Syntax.Tm_refine uu____12255 in
                        mk uu____12254 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains Weak cfg.steps
               then
                 let uu____12283 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____12283
               else
                 (let uu____12285 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____12285 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12293 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12305  -> Dummy :: env1) env) in
                        norm_comp cfg uu____12293 c1 in
                      let t2 =
                        let uu____12315 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____12315 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____12374)::uu____12375 ->
                    (log cfg
                       (fun uu____12386  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | (Arg uu____12387)::uu____12388 ->
                    (log cfg
                       (fun uu____12399  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | (App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____12400;
                       FStar_Syntax_Syntax.vars = uu____12401;_},uu____12402,uu____12403))::uu____12404
                    ->
                    (log cfg
                       (fun uu____12413  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | (MemoLazy uu____12414)::uu____12415 ->
                    (log cfg
                       (fun uu____12426  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | uu____12427 ->
                    (log cfg
                       (fun uu____12430  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11 in
                      log cfg
                        (fun uu____12434  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____12451 = norm cfg env [] t2 in
                             FStar_Util.Inl uu____12451
                         | FStar_Util.Inr c ->
                             let uu____12459 = norm_comp cfg env c in
                             FStar_Util.Inr uu____12459 in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env []) in
                       let uu____12465 =
                         let uu____12466 =
                           let uu____12467 =
                             let uu____12494 =
                               FStar_Syntax_Util.unascribe t12 in
                             (uu____12494, (tc1, tacopt1), l) in
                           FStar_Syntax_Syntax.Tm_ascribed uu____12467 in
                         mk uu____12466 t1.FStar_Syntax_Syntax.pos in
                       rebuild cfg env stack1 uu____12465))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____12570,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____12571;
                               FStar_Syntax_Syntax.lbunivs = uu____12572;
                               FStar_Syntax_Syntax.lbtyp = uu____12573;
                               FStar_Syntax_Syntax.lbeff = uu____12574;
                               FStar_Syntax_Syntax.lbdef = uu____12575;_}::uu____12576),uu____12577)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____12613 =
                 (let uu____12616 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____12616) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____12618 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____12618))) in
               if uu____12613
               then
                 let env1 =
                   let uu____12622 =
                     let uu____12623 =
                       let uu____12642 =
                         FStar_Util.mk_ref FStar_Pervasives_Native.None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____12642,
                         false) in
                     Clos uu____12623 in
                   uu____12622 :: env in
                 (log cfg
                    (fun uu____12695  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack1 body)
               else
                 (let uu____12697 =
                    let uu____12702 =
                      let uu____12703 =
                        let uu____12704 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____12704
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____12703] in
                    FStar_Syntax_Subst.open_term uu____12702 body in
                  match uu____12697 with
                  | (bs,body1) ->
                      (log cfg
                         (fun uu____12713  ->
                            FStar_Util.print_string
                              "+++ Normalizing Tm_let -- type\n");
                       (let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let lbname =
                          let x =
                            let uu____12721 = FStar_List.hd bs in
                            FStar_Pervasives_Native.fst uu____12721 in
                          FStar_Util.Inl
                            (let uu___214_12731 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___214_12731.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___214_12731.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = ty
                             }) in
                        log cfg
                          (fun uu____12734  ->
                             FStar_Util.print_string
                               "+++ Normalizing Tm_let -- definiens\n");
                        (let lb1 =
                           let uu___215_12736 = lb in
                           let uu____12737 =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname = lbname;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___215_12736.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = ty;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___215_12736.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____12737
                           } in
                         let env' =
                           FStar_All.pipe_right bs
                             (FStar_List.fold_left
                                (fun env1  ->
                                   fun uu____12754  -> Dummy :: env1) env) in
                         let cfg1 = only_strong_steps cfg in
                         log cfg1
                           (fun uu____12764  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- body\n");
                         norm cfg1 env'
                           ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1) body1))))
           | FStar_Syntax_Syntax.Tm_let ((true ,lbs),body) when
               (FStar_List.contains CompressUvars cfg.steps) ||
                 ((FStar_List.contains (Exclude Zeta) cfg.steps) &&
                    (FStar_List.contains PureSubtermsWithinComputations
                       cfg.steps))
               ->
               let uu____12781 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____12781 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____12817 =
                               let uu___216_12818 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___216_12818.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___216_12818.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____12817 in
                           let uu____12819 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____12819 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____12839 =
                                   FStar_List.map (fun uu____12843  -> Dummy)
                                     lbs1 in
                                 let uu____12844 =
                                   let uu____12847 =
                                     FStar_List.map
                                       (fun uu____12855  -> Dummy) xs1 in
                                   FStar_List.append uu____12847 env in
                                 FStar_List.append uu____12839 uu____12844 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____12867 =
                                       let uu___217_12868 = rc in
                                       let uu____12869 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___217_12868.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____12869;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___217_12868.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____12867
                                 | uu____12876 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___218_12880 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___218_12880.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___218_12880.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____12884 =
                        FStar_List.map (fun uu____12888  -> Dummy) lbs2 in
                      FStar_List.append uu____12884 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____12890 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____12890 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___219_12906 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___219_12906.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___219_12906.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____12933 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____12933
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____12952 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13003  ->
                        match uu____13003 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____13076 =
                                let uu___220_13077 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___220_13077.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___220_13077.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____13076 in
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
               (match uu____12952 with
                | (rec_env,memos,uu____13205) ->
                    let uu____13234 =
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
                             let uu____13699 =
                               let uu____13700 =
                                 let uu____13719 =
                                   FStar_Util.mk_ref
                                     FStar_Pervasives_Native.None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____13719, false) in
                               Clos uu____13700 in
                             uu____13699 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
                    norm cfg body_env stack1 body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (match m with
                | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                    let uu____13786 =
                      let uu____13787 = should_reify cfg stack1 in
                      Prims.op_Negation uu____13787 in
                    if uu____13786
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____13797 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____13797
                        then
                          let uu___221_13798 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___221_13798.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps =
                              (uu___221_13798.primitive_steps)
                          }
                        else
                          (let uu___222_13800 = cfg in
                           {
                             steps =
                               (FStar_List.append [Exclude Zeta] cfg.steps);
                             tcenv = (uu___222_13800.tcenv);
                             delta_level = (uu___222_13800.delta_level);
                             primitive_steps =
                               (uu___222_13800.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____13802 =
                         let uu____13803 = FStar_Syntax_Subst.compress head1 in
                         uu____13803.FStar_Syntax_Syntax.n in
                       match uu____13802 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____13821 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____13821 with
                            | (uu____13822,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____13828 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____13836 =
                                         let uu____13837 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____13837.FStar_Syntax_Syntax.n in
                                       match uu____13836 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____13843,uu____13844))
                                           ->
                                           let uu____13853 =
                                             let uu____13854 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____13854.FStar_Syntax_Syntax.n in
                                           (match uu____13853 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____13860,msrc,uu____13862))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____13871 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____13871
                                            | uu____13872 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____13873 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____13874 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____13874 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___223_13879 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___223_13879.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___223_13879.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___223_13879.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____13880 =
                                            FStar_List.tl stack1 in
                                          let uu____13881 =
                                            let uu____13882 =
                                              let uu____13885 =
                                                let uu____13886 =
                                                  let uu____13899 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____13899) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____13886 in
                                              FStar_Syntax_Syntax.mk
                                                uu____13885 in
                                            uu____13882
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____13880
                                            uu____13881
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____13915 =
                                            let uu____13916 = is_return body in
                                            match uu____13916 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____13920;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____13921;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____13926 -> false in
                                          if uu____13915
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
                                               let uu____13950 =
                                                 let uu____13953 =
                                                   let uu____13954 =
                                                     let uu____13971 =
                                                       let uu____13974 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____13974] in
                                                     (uu____13971, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc)) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____13954 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____13953 in
                                               uu____13950
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____13990 =
                                                 let uu____13991 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____13991.FStar_Syntax_Syntax.n in
                                               match uu____13990 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____13997::uu____13998::[])
                                                   ->
                                                   let uu____14005 =
                                                     let uu____14008 =
                                                       let uu____14009 =
                                                         let uu____14016 =
                                                           let uu____14019 =
                                                             let uu____14020
                                                               =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____14020 in
                                                           let uu____14021 =
                                                             let uu____14024
                                                               =
                                                               let uu____14025
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____14025 in
                                                             [uu____14024] in
                                                           uu____14019 ::
                                                             uu____14021 in
                                                         (bind1, uu____14016) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____14009 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____14008 in
                                                   uu____14005
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____14033 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____14039 =
                                                 let uu____14042 =
                                                   let uu____14043 =
                                                     let uu____14058 =
                                                       let uu____14061 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____14062 =
                                                         let uu____14065 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____14066 =
                                                           let uu____14069 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____14070 =
                                                             let uu____14073
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____14074
                                                               =
                                                               let uu____14077
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____14078
                                                                 =
                                                                 let uu____14081
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____14081] in
                                                               uu____14077 ::
                                                                 uu____14078 in
                                                             uu____14073 ::
                                                               uu____14074 in
                                                           uu____14069 ::
                                                             uu____14070 in
                                                         uu____14065 ::
                                                           uu____14066 in
                                                       uu____14061 ::
                                                         uu____14062 in
                                                     (bind_inst, uu____14058) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____14043 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____14042 in
                                               uu____14039
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____14089 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____14089 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____14113 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____14113 with
                            | (uu____14114,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____14149 =
                                        let uu____14150 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____14150.FStar_Syntax_Syntax.n in
                                      match uu____14149 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____14156) -> t4
                                      | uu____14161 -> head2 in
                                    let uu____14162 =
                                      let uu____14163 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____14163.FStar_Syntax_Syntax.n in
                                    match uu____14162 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____14169 ->
                                        FStar_Pervasives_Native.None in
                                  let uu____14170 = maybe_extract_fv head2 in
                                  match uu____14170 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____14180 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____14180
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____14185 =
                                          maybe_extract_fv head3 in
                                        match uu____14185 with
                                        | FStar_Pervasives_Native.Some
                                            uu____14190 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____14191 ->
                                            FStar_Pervasives_Native.Some
                                              false in
                                      (head3, action_unfolded)
                                  | uu____14196 ->
                                      (head2, FStar_Pervasives_Native.None) in
                                ((let is_arg_impure uu____14211 =
                                    match uu____14211 with
                                    | (e,q) ->
                                        let uu____14218 =
                                          let uu____14219 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____14219.FStar_Syntax_Syntax.n in
                                        (match uu____14218 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____14234 -> false) in
                                  let uu____14235 =
                                    let uu____14236 =
                                      let uu____14243 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____14243 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____14236 in
                                  if uu____14235
                                  then
                                    let uu____14248 =
                                      let uu____14249 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____14249 in
                                    failwith uu____14248
                                  else ());
                                 (let uu____14251 =
                                    maybe_unfold_action head_app in
                                  match uu____14251 with
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
                                      let uu____14290 = FStar_List.tl stack1 in
                                      norm cfg env uu____14290 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____14304 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____14304 in
                           let uu____14305 = FStar_List.tl stack1 in
                           norm cfg env uu____14305 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____14426  ->
                                     match uu____14426 with
                                     | (pat,wopt,tm) ->
                                         let uu____14474 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____14474))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____14506 = FStar_List.tl stack1 in
                           norm cfg env uu____14506 tm
                       | uu____14507 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let uu____14515 = should_reify cfg stack1 in
                    if uu____14515
                    then
                      let uu____14516 = FStar_List.tl stack1 in
                      let uu____14517 =
                        let uu____14518 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____14518 in
                      norm cfg env uu____14516 uu____14517
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____14521 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____14521
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___224_14530 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___224_14530.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___224_14530.primitive_steps)
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
                | uu____14532 ->
                    if FStar_List.contains Unmeta cfg.steps
                    then norm cfg env stack1 head1
                    else
                      (match stack1 with
                       | uu____14534::uu____14535 ->
                           (match m with
                            | FStar_Syntax_Syntax.Meta_labeled
                                (l,r,uu____14540) ->
                                norm cfg env ((Meta (m, r)) :: stack1) head1
                            | FStar_Syntax_Syntax.Meta_alien uu____14541 ->
                                rebuild cfg env stack1 t1
                            | FStar_Syntax_Syntax.Meta_pattern args ->
                                let args1 = norm_pattern_args cfg env args in
                                norm cfg env
                                  ((Meta
                                      ((FStar_Syntax_Syntax.Meta_pattern
                                          args1),
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) head1
                            | uu____14572 -> norm cfg env stack1 head1)
                       | [] ->
                           let head2 = norm cfg env [] head1 in
                           let m1 =
                             match m with
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let uu____14586 =
                                   norm_pattern_args cfg env args in
                                 FStar_Syntax_Syntax.Meta_pattern uu____14586
                             | uu____14597 -> m in
                           let t2 =
                             mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                               t1.FStar_Syntax_Syntax.pos in
                           rebuild cfg env stack1 t2)))
and do_unfold_fv:
  cfg ->
    env ->
      stack_elt Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun t0  ->
          fun f  ->
            let r_env =
              let uu____14609 = FStar_Syntax_Syntax.range_of_fv f in
              FStar_TypeChecker_Env.set_range cfg.tcenv uu____14609 in
            let uu____14610 =
              FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            match uu____14610 with
            | FStar_Pervasives_Native.None  ->
                (log cfg
                   (fun uu____14623  ->
                      FStar_Util.print "Tm_fvar case 2\n" []);
                 rebuild cfg env stack1 t0)
            | FStar_Pervasives_Native.Some (us,t) ->
                (log cfg
                   (fun uu____14634  ->
                      let uu____14635 = FStar_Syntax_Print.term_to_string t0 in
                      let uu____14636 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____14635
                        uu____14636);
                 (let t1 =
                    let uu____14638 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.contains
                           (UnfoldUntil FStar_Syntax_Syntax.Delta_constant)) in
                    if uu____14638
                    then t
                    else
                      FStar_Syntax_Subst.set_use_range
                        (FStar_Ident.range_of_lid
                           (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                        t in
                  let n1 = FStar_List.length us in
                  if n1 > (Prims.parse_int "0")
                  then
                    match stack1 with
                    | (UnivArgs (us',uu____14648))::stack2 ->
                        let env1 =
                          FStar_All.pipe_right us'
                            (FStar_List.fold_left
                               (fun env1  -> fun u  -> (Univ u) :: env1) env) in
                        norm cfg env1 stack2 t1
                    | uu____14671 when
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains EraseUniverses)
                        -> norm cfg env stack1 t1
                    | uu____14674 ->
                        let uu____14677 =
                          let uu____14678 =
                            FStar_Syntax_Print.lid_to_string
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                          FStar_Util.format1
                            "Impossible: missing universe instantiation on %s"
                            uu____14678 in
                        failwith uu____14677
                  else norm cfg env stack1 t1))
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
              let uu____14688 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____14688 with
              | (uu____14689,return_repr) ->
                  let return_inst =
                    let uu____14698 =
                      let uu____14699 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____14699.FStar_Syntax_Syntax.n in
                    match uu____14698 with
                    | FStar_Syntax_Syntax.Tm_uinst
                        (return_tm,uu____14705::[]) ->
                        let uu____14712 =
                          let uu____14715 =
                            let uu____14716 =
                              let uu____14723 =
                                let uu____14726 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____14726] in
                              (return_tm, uu____14723) in
                            FStar_Syntax_Syntax.Tm_uinst uu____14716 in
                          FStar_Syntax_Syntax.mk uu____14715 in
                        uu____14712 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____14734 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____14737 =
                    let uu____14740 =
                      let uu____14741 =
                        let uu____14756 =
                          let uu____14759 = FStar_Syntax_Syntax.as_arg t in
                          let uu____14760 =
                            let uu____14763 = FStar_Syntax_Syntax.as_arg e in
                            [uu____14763] in
                          uu____14759 :: uu____14760 in
                        (return_inst, uu____14756) in
                      FStar_Syntax_Syntax.Tm_app uu____14741 in
                    FStar_Syntax_Syntax.mk uu____14740 in
                  uu____14737 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____14772 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____14772 with
               | FStar_Pervasives_Native.None  ->
                   let uu____14775 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____14775
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____14776;
                     FStar_TypeChecker_Env.mtarget = uu____14777;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____14778;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____14789;
                     FStar_TypeChecker_Env.mtarget = uu____14790;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____14791;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____14809 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____14809)
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
                (fun uu____14865  ->
                   match uu____14865 with
                   | (a,imp) ->
                       let uu____14876 = norm cfg env [] a in
                       (uu____14876, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___225_14893 = comp1 in
            let uu____14896 =
              let uu____14897 =
                let uu____14906 = norm cfg env [] t in
                let uu____14907 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____14906, uu____14907) in
              FStar_Syntax_Syntax.Total uu____14897 in
            {
              FStar_Syntax_Syntax.n = uu____14896;
              FStar_Syntax_Syntax.pos =
                (uu___225_14893.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___225_14893.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___226_14922 = comp1 in
            let uu____14925 =
              let uu____14926 =
                let uu____14935 = norm cfg env [] t in
                let uu____14936 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____14935, uu____14936) in
              FStar_Syntax_Syntax.GTotal uu____14926 in
            {
              FStar_Syntax_Syntax.n = uu____14925;
              FStar_Syntax_Syntax.pos =
                (uu___226_14922.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___226_14922.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____14988  ->
                      match uu____14988 with
                      | (a,i) ->
                          let uu____14999 = norm cfg env [] a in
                          (uu____14999, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___179_15010  ->
                      match uu___179_15010 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____15014 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____15014
                      | f -> f)) in
            let uu___227_15018 = comp1 in
            let uu____15021 =
              let uu____15022 =
                let uu___228_15023 = ct in
                let uu____15024 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____15025 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____15028 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____15024;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___228_15023.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____15025;
                  FStar_Syntax_Syntax.effect_args = uu____15028;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____15022 in
            {
              FStar_Syntax_Syntax.n = uu____15021;
              FStar_Syntax_Syntax.pos =
                (uu___227_15018.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___227_15018.FStar_Syntax_Syntax.vars)
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
            (let uu___229_15046 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___229_15046.tcenv);
               delta_level = (uu___229_15046.delta_level);
               primitive_steps = (uu___229_15046.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____15051 = norm1 t in
          FStar_Syntax_Util.non_informative uu____15051 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____15054 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___230_15073 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.pos =
                (uu___230_15073.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___230_15073.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____15080 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____15080
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
                    let uu___231_15091 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___231_15091.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___231_15091.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___231_15091.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___232_15093 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___232_15093.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___232_15093.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___232_15093.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___232_15093.FStar_Syntax_Syntax.flags)
                    } in
              let uu___233_15094 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos =
                  (uu___233_15094.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___233_15094.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____15096 -> c
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____15099  ->
        match uu____15099 with
        | (x,imp) ->
            let uu____15102 =
              let uu___234_15103 = x in
              let uu____15104 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___234_15103.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___234_15103.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____15104
              } in
            (uu____15102, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____15110 =
          FStar_List.fold_left
            (fun uu____15128  ->
               fun b  ->
                 match uu____15128 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____15110 with | (nbs,uu____15156) -> FStar_List.rev nbs
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
            let uu____15172 =
              let uu___235_15173 = rc in
              let uu____15174 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___235_15173.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____15174;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___235_15173.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____15172
        | uu____15181 -> lopt
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
              ((let uu____15194 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____15194
                then
                  let time_now = FStar_Util.now () in
                  let uu____15196 =
                    let uu____15197 =
                      let uu____15198 =
                        FStar_Util.time_diff time_then time_now in
                      FStar_Pervasives_Native.snd uu____15198 in
                    FStar_Util.string_of_int uu____15197 in
                  let uu____15203 = FStar_Syntax_Print.term_to_string tm in
                  let uu____15204 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                    uu____15196 uu____15203 uu____15204
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___236_15222 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___236_15222.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____15315  ->
                    let uu____15316 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____15316);
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
              let uu____15352 =
                let uu___237_15353 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___237_15353.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___237_15353.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____15352
          | (Arg (Univ uu____15354,uu____15355,uu____15356))::uu____15357 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____15360,uu____15361))::uu____15362 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____15378),aq,r))::stack2 ->
              (log cfg
                 (fun uu____15407  ->
                    let uu____15408 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____15408);
               if FStar_List.contains (Exclude Iota) cfg.steps
               then
                 (if FStar_List.contains HNF cfg.steps
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
                 (let uu____15418 = FStar_ST.op_Bang m in
                  match uu____15418 with
                  | FStar_Pervasives_Native.None  ->
                      if FStar_List.contains HNF cfg.steps
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
                  | FStar_Pervasives_Native.Some (uu____15538,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq)
                          FStar_Pervasives_Native.None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 =
                FStar_Syntax_Syntax.extend_app head1 (t, aq)
                  FStar_Pervasives_Native.None r in
              let uu____15562 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____15562
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____15572  ->
                    let uu____15573 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____15573);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____15578 =
                  log cfg
                    (fun uu____15583  ->
                       let uu____15584 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____15585 =
                         let uu____15586 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____15603  ->
                                   match uu____15603 with
                                   | (p,uu____15613,uu____15614) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____15586
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____15584 uu____15585);
                  (let whnf =
                     (FStar_List.contains Weak cfg.steps) ||
                       (FStar_List.contains HNF cfg.steps) in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___180_15631  ->
                               match uu___180_15631 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____15632 -> false)) in
                     let steps' =
                       let uu____15636 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____15636
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     only_strong_steps
                       (let uu___238_15642 = cfg in
                        {
                          steps = (FStar_List.append steps' cfg.steps);
                          tcenv = (uu___238_15642.tcenv);
                          delta_level = new_delta;
                          primitive_steps = (uu___238_15642.primitive_steps)
                        }) in
                   let norm_or_whnf env2 t1 =
                     if whnf
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____15686 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____15709 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____15775  ->
                                   fun uu____15776  ->
                                     match (uu____15775, uu____15776) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____15879 = norm_pat env3 p1 in
                                         (match uu____15879 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____15709 with
                          | (pats1,env3) ->
                              ((let uu___239_15981 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.p =
                                    (uu___239_15981.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___240_16000 = x in
                           let uu____16001 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___240_16000.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___240_16000.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16001
                           } in
                         ((let uu___241_16009 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.p =
                               (uu___241_16009.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___242_16014 = x in
                           let uu____16015 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___242_16014.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___242_16014.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16015
                           } in
                         ((let uu___243_16023 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.p =
                               (uu___243_16023.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___244_16033 = x in
                           let uu____16034 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___244_16033.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___244_16033.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16034
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___245_16043 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.p =
                               (uu___245_16043.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf -> branches
                     | uu____16047 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____16061 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____16061 with
                                 | (p,wopt,e) ->
                                     let uu____16081 = norm_pat env1 p in
                                     (match uu____16081 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Pervasives_Native.Some w
                                                ->
                                                let uu____16112 =
                                                  norm_or_whnf env2 w in
                                                FStar_Pervasives_Native.Some
                                                  uu____16112 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____16118 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____16118) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____16128) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____16133 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____16134;
                        FStar_Syntax_Syntax.fv_delta = uu____16135;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Data_ctor );_}
                      -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____16136;
                        FStar_Syntax_Syntax.fv_delta = uu____16137;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Record_ctor uu____16138);_}
                      -> true
                  | uu____16145 -> false in
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
                  let uu____16274 =
                    FStar_Syntax_Util.head_and_args scrutinee1 in
                  match uu____16274 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var uu____16323 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_wild uu____16326 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____16329 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee1.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____16348 ->
                                let uu____16349 =
                                  let uu____16350 = is_cons head1 in
                                  Prims.op_Negation uu____16350 in
                                FStar_Util.Inr uu____16349)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____16371 =
                             let uu____16372 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____16372.FStar_Syntax_Syntax.n in
                           (match uu____16371 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____16382 ->
                                let uu____16383 =
                                  let uu____16384 = is_cons head1 in
                                  Prims.op_Negation uu____16384 in
                                FStar_Util.Inr uu____16383))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____16437)::rest_a,(p1,uu____16440)::rest_p) ->
                      let uu____16484 = matches_pat t1 p1 in
                      (match uu____16484 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____16509 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____16611 = matches_pat scrutinee1 p1 in
                      (match uu____16611 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____16631  ->
                                 let uu____16632 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____16633 =
                                   let uu____16634 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____16634
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____16632 uu____16633);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____16651 =
                                        let uu____16652 =
                                          let uu____16671 =
                                            FStar_Util.mk_ref
                                              (FStar_Pervasives_Native.Some
                                                 ([], t1)) in
                                          ([], t1, uu____16671, false) in
                                        Clos uu____16652 in
                                      uu____16651 :: env2) env1 s in
                             let uu____16724 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____16724))) in
                let uu____16725 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____16725
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___181_16748  ->
                match uu___181_16748 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____16752 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____16758 -> d in
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
            let uu___246_16787 = config s e in
            {
              steps = (uu___246_16787.steps);
              tcenv = (uu___246_16787.tcenv);
              delta_level = (uu___246_16787.delta_level);
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
      fun t  -> let uu____16812 = config s e in norm_comp uu____16812 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____16821 = config [] env in norm_universe uu____16821 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let uu____16830 = config [] env in ghost_to_pure_aux uu____16830 [] c
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
        let uu____16844 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____16844 in
      let uu____16845 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____16845
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___247_16847 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___247_16847.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___247_16847.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____16850  ->
                    let uu____16851 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____16851))
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
            ((let uu____16870 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning
                "Normalization failed with error %s\n" uu____16870);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____16883 = config [AllowUnboundUniverses] env in
          norm_comp uu____16883 [] c
        with
        | e ->
            ((let uu____16890 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning
                "Normalization failed with error %s\n" uu____16890);
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
                   let uu____16930 =
                     let uu____16931 =
                       let uu____16938 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____16938) in
                     FStar_Syntax_Syntax.Tm_refine uu____16931 in
                   mk uu____16930 t01.FStar_Syntax_Syntax.pos
               | uu____16943 -> t2)
          | uu____16944 -> t2 in
        aux t
let unfold_whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      normalize
        [Weak; HNF; UnfoldUntil FStar_Syntax_Syntax.Delta_constant; Beta] env
        t
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
        let uu____16996 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____16996 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____17025 ->
                 let uu____17032 = FStar_Syntax_Util.abs_formals e in
                 (match uu____17032 with
                  | (actuals,uu____17042,uu____17043) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____17057 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____17057 with
                         | (binders,args) ->
                             let uu____17074 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____17074
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
      | uu____17084 ->
          let uu____17085 = FStar_Syntax_Util.head_and_args t in
          (match uu____17085 with
           | (head1,args) ->
               let uu____17122 =
                 let uu____17123 = FStar_Syntax_Subst.compress head1 in
                 uu____17123.FStar_Syntax_Syntax.n in
               (match uu____17122 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____17126,thead) ->
                    let uu____17152 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____17152 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____17194 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___252_17202 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___252_17202.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___252_17202.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___252_17202.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___252_17202.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___252_17202.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___252_17202.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___252_17202.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___252_17202.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___252_17202.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___252_17202.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___252_17202.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___252_17202.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___252_17202.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___252_17202.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___252_17202.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___252_17202.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___252_17202.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___252_17202.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___252_17202.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___252_17202.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___252_17202.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___252_17202.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___252_17202.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___252_17202.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___252_17202.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___252_17202.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___252_17202.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___252_17202.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___252_17202.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___252_17202.FStar_TypeChecker_Env.dsenv)
                                 }) t in
                            match uu____17194 with
                            | (uu____17203,ty,uu____17205) ->
                                eta_expand_with_type env t ty))
                | uu____17206 ->
                    let uu____17207 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___253_17215 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___253_17215.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___253_17215.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___253_17215.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___253_17215.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___253_17215.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___253_17215.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___253_17215.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___253_17215.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___253_17215.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___253_17215.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___253_17215.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___253_17215.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___253_17215.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___253_17215.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___253_17215.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___253_17215.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___253_17215.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___253_17215.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___253_17215.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___253_17215.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___253_17215.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___253_17215.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___253_17215.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___253_17215.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___253_17215.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___253_17215.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___253_17215.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___253_17215.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___253_17215.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___253_17215.FStar_TypeChecker_Env.dsenv)
                         }) t in
                    (match uu____17207 with
                     | (uu____17216,ty,uu____17218) ->
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
            | (uu____17296,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____17302,FStar_Util.Inl t) ->
                let uu____17308 =
                  let uu____17311 =
                    let uu____17312 =
                      let uu____17325 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____17325) in
                    FStar_Syntax_Syntax.Tm_arrow uu____17312 in
                  FStar_Syntax_Syntax.mk uu____17311 in
                uu____17308 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____17329 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____17329 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____17356 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____17411 ->
                    let uu____17412 =
                      let uu____17421 =
                        let uu____17422 = FStar_Syntax_Subst.compress t3 in
                        uu____17422.FStar_Syntax_Syntax.n in
                      (uu____17421, tc) in
                    (match uu____17412 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____17447) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____17484) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____17523,FStar_Util.Inl uu____17524) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____17547 -> failwith "Impossible") in
              (match uu____17356 with
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
          let uu____17656 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____17656 with
          | (univ_names1,binders1,tc) ->
              let uu____17714 = FStar_Util.left tc in
              (univ_names1, binders1, uu____17714)
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
          let uu____17753 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____17753 with
          | (univ_names1,binders1,tc) ->
              let uu____17813 = FStar_Util.right tc in
              (univ_names1, binders1, uu____17813)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____17848 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____17848 with
           | (univ_names1,binders1,typ1) ->
               let uu___254_17876 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___254_17876.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___254_17876.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___254_17876.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___254_17876.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___255_17897 = s in
          let uu____17898 =
            let uu____17899 =
              let uu____17908 = FStar_List.map (elim_uvars env) sigs in
              (uu____17908, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____17899 in
          {
            FStar_Syntax_Syntax.sigel = uu____17898;
            FStar_Syntax_Syntax.sigrng =
              (uu___255_17897.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___255_17897.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___255_17897.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___255_17897.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____17925 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____17925 with
           | (univ_names1,uu____17943,typ1) ->
               let uu___256_17957 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___256_17957.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___256_17957.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___256_17957.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___256_17957.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____17963 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____17963 with
           | (univ_names1,uu____17981,typ1) ->
               let uu___257_17995 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___257_17995.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___257_17995.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___257_17995.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___257_17995.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____18029 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____18029 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____18052 =
                            let uu____18053 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____18053 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____18052 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___258_18056 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___258_18056.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___258_18056.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___259_18057 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___259_18057.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___259_18057.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___259_18057.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___259_18057.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___260_18069 = s in
          let uu____18070 =
            let uu____18071 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____18071 in
          {
            FStar_Syntax_Syntax.sigel = uu____18070;
            FStar_Syntax_Syntax.sigrng =
              (uu___260_18069.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___260_18069.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___260_18069.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___260_18069.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____18075 = elim_uvars_aux_t env us [] t in
          (match uu____18075 with
           | (us1,uu____18093,t1) ->
               let uu___261_18107 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___261_18107.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___261_18107.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___261_18107.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___261_18107.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____18108 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____18110 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____18110 with
           | (univs1,binders,signature) ->
               let uu____18138 =
                 let uu____18147 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____18147 with
                 | (univs_opening,univs2) ->
                     let uu____18174 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____18174) in
               (match uu____18138 with
                | (univs_opening,univs_closing) ->
                    let uu____18191 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____18197 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____18198 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____18197, uu____18198) in
                    (match uu____18191 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____18220 =
                           match uu____18220 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____18238 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____18238 with
                                | (us1,t1) ->
                                    let uu____18249 =
                                      let uu____18254 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____18261 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____18254, uu____18261) in
                                    (match uu____18249 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____18274 =
                                           let uu____18279 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____18288 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____18279, uu____18288) in
                                         (match uu____18274 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____18304 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____18304 in
                                              let uu____18305 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____18305 with
                                               | (uu____18326,uu____18327,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____18342 =
                                                       let uu____18343 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____18343 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____18342 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____18348 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____18348 with
                           | (uu____18361,uu____18362,t1) -> t1 in
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
                             | uu____18422 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____18439 =
                               let uu____18440 =
                                 FStar_Syntax_Subst.compress body in
                               uu____18440.FStar_Syntax_Syntax.n in
                             match uu____18439 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____18499 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____18528 =
                               let uu____18529 =
                                 FStar_Syntax_Subst.compress t in
                               uu____18529.FStar_Syntax_Syntax.n in
                             match uu____18528 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____18550) ->
                                 let uu____18571 = destruct_action_body body in
                                 (match uu____18571 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____18616 ->
                                 let uu____18617 = destruct_action_body t in
                                 (match uu____18617 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____18666 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____18666 with
                           | (action_univs,t) ->
                               let uu____18675 = destruct_action_typ_templ t in
                               (match uu____18675 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___262_18716 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___262_18716.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___262_18716.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___263_18718 = ed in
                           let uu____18719 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____18720 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____18721 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____18722 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____18723 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____18724 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____18725 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____18726 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____18727 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____18728 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____18729 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____18730 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____18731 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____18732 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___263_18718.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___263_18718.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____18719;
                             FStar_Syntax_Syntax.bind_wp = uu____18720;
                             FStar_Syntax_Syntax.if_then_else = uu____18721;
                             FStar_Syntax_Syntax.ite_wp = uu____18722;
                             FStar_Syntax_Syntax.stronger = uu____18723;
                             FStar_Syntax_Syntax.close_wp = uu____18724;
                             FStar_Syntax_Syntax.assert_p = uu____18725;
                             FStar_Syntax_Syntax.assume_p = uu____18726;
                             FStar_Syntax_Syntax.null_wp = uu____18727;
                             FStar_Syntax_Syntax.trivial = uu____18728;
                             FStar_Syntax_Syntax.repr = uu____18729;
                             FStar_Syntax_Syntax.return_repr = uu____18730;
                             FStar_Syntax_Syntax.bind_repr = uu____18731;
                             FStar_Syntax_Syntax.actions = uu____18732
                           } in
                         let uu___264_18735 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___264_18735.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___264_18735.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___264_18735.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___264_18735.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___182_18752 =
            match uu___182_18752 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____18779 = elim_uvars_aux_t env us [] t in
                (match uu____18779 with
                 | (us1,uu____18803,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___265_18822 = sub_eff in
            let uu____18823 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____18826 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___265_18822.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___265_18822.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____18823;
              FStar_Syntax_Syntax.lift = uu____18826
            } in
          let uu___266_18829 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___266_18829.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___266_18829.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___266_18829.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___266_18829.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____18839 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____18839 with
           | (univ_names1,binders1,comp1) ->
               let uu___267_18873 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___267_18873.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___267_18873.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___267_18873.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___267_18873.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____18884 -> s