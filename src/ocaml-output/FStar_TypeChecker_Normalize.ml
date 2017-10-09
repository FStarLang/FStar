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
  fun uu___167_395  ->
    match uu___167_395 with
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
let only_strong_steps':
  primitive_step Prims.list -> primitive_step Prims.list =
  fun steps  -> FStar_List.filter (fun ps  -> ps.strong_reduction_ok) steps
let only_strong_steps: cfg -> cfg =
  fun cfg  ->
    let uu___183_513 = cfg in
    let uu____514 = only_strong_steps' cfg.primitive_steps in
    {
      steps = (uu___183_513.steps);
      tcenv = (uu___183_513.tcenv);
      delta_level = (uu___183_513.delta_level);
      primitive_steps = uu____514
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
    match projectee with | Arg _0 -> true | uu____661 -> false
let __proj__Arg__item___0:
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Arg _0 -> _0
let uu___is_UnivArgs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____699 -> false
let __proj__UnivArgs__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____737 -> false
let __proj__MemoLazy__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0
let uu___is_Match: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____796 -> false
let __proj__Match__item___0:
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Abs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____840 -> false
let __proj__Abs__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____896 -> false
let __proj__App__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Meta: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____932 -> false
let __proj__Meta__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Meta _0 -> _0
let uu___is_Let: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____966 -> false
let __proj__Let__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Steps: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Steps _0 -> true | uu____1014 -> false
let __proj__Steps__item___0:
  stack_elt ->
    (steps,primitive_step Prims.list,FStar_TypeChecker_Env.delta_level
                                       Prims.list)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Steps _0 -> _0
let uu___is_Debug: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____1062 -> false
let __proj__Debug__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list[@@deriving show]
let mk:
  'Auu____1091 .
    'Auu____1091 ->
      FStar_Range.range -> 'Auu____1091 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r
let set_memo:
  'Auu____1248 'Auu____1249 .
    ('Auu____1249 FStar_Pervasives_Native.option,'Auu____1248) FStar_ST.mref
      -> 'Auu____1249 -> Prims.unit
  =
  fun r  ->
    fun t  ->
      let uu____1544 = FStar_ST.op_Bang r in
      match uu____1544 with
      | FStar_Pervasives_Native.Some uu____1645 ->
          failwith "Unexpected set_memo: thunk already evaluated"
      | FStar_Pervasives_Native.None  ->
          FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____1752 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____1752 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___168_1760  ->
    match uu___168_1760 with
    | Arg (c,uu____1762,uu____1763) ->
        let uu____1764 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____1764
    | MemoLazy uu____1765 -> "MemoLazy"
    | Abs (uu____1772,bs,uu____1774,uu____1775,uu____1776) ->
        let uu____1781 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____1781
    | UnivArgs uu____1786 -> "UnivArgs"
    | Match uu____1793 -> "Match"
    | App (t,uu____1801,uu____1802) ->
        let uu____1803 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____1803
    | Meta (m,uu____1805) -> "Meta"
    | Let uu____1806 -> "Let"
    | Steps (uu____1815,uu____1816,uu____1817) -> "Steps"
    | Debug (t,uu____1827) ->
        let uu____1828 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____1828
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____1837 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____1837 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1855 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____1855 then f () else ()
let is_empty: 'Auu____1861 . 'Auu____1861 Prims.list -> Prims.bool =
  fun uu___169_1867  ->
    match uu___169_1867 with | [] -> true | uu____1870 -> false
let lookup_bvar:
  'Auu____1879 .
    'Auu____1879 Prims.list -> FStar_Syntax_Syntax.bv -> 'Auu____1879
  =
  fun env  ->
    fun x  ->
      try FStar_List.nth env x.FStar_Syntax_Syntax.index
      with
      | uu____1898 ->
          let uu____1899 =
            let uu____1900 = FStar_Syntax_Print.db_to_string x in
            FStar_Util.format1 "Failed to find %s\n" uu____1900 in
          failwith uu____1899
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
          let uu____1945 =
            FStar_List.fold_left
              (fun uu____1971  ->
                 fun u1  ->
                   match uu____1971 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____1996 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____1996 with
                        | (k_u,n1) ->
                            let uu____2011 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____2011
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____1945 with
          | (uu____2029,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____2054 = FStar_List.nth env x in
                 match uu____2054 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____2058 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____2067 ->
                   let uu____2068 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____2068
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____2074 when
              FStar_All.pipe_right cfg.steps
                (FStar_List.contains CheckNoUvars)
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____2083 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____2092 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____2099 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____2099 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____2116 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____2116 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____2124 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____2132 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____2132 with
                                  | (uu____2137,m) -> n1 <= m)) in
                        if uu____2124 then rest1 else us1
                    | uu____2142 -> us1)
               | uu____2147 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____2151 = aux u3 in
              FStar_List.map (fun _0_42  -> FStar_Syntax_Syntax.U_succ _0_42)
                uu____2151 in
        let uu____2154 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____2154
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____2156 = aux u in
           match uu____2156 with
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
          (fun uu____2276  ->
             let uu____2277 = FStar_Syntax_Print.tag_of_term t in
             let uu____2278 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____2277
               uu____2278);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____2279 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____2283 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____2308 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____2309 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____2310 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____2311 ->
                  let uu____2328 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains CheckNoUvars) in
                  if uu____2328
                  then
                    let uu____2329 =
                      let uu____2330 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos in
                      let uu____2331 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____2330 uu____2331 in
                    failwith uu____2329
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____2334 =
                    let uu____2335 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____2335 in
                  mk uu____2334 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____2342 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____2342
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____2344 = lookup_bvar env x in
                  (match uu____2344 with
                   | Univ uu____2345 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____2349) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____2437 = closures_as_binders_delayed cfg env bs in
                  (match uu____2437 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____2471 =
                         let uu____2472 =
                           let uu____2489 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____2489) in
                         FStar_Syntax_Syntax.Tm_abs uu____2472 in
                       mk uu____2471 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____2520 = closures_as_binders_delayed cfg env bs in
                  (match uu____2520 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____2568 =
                    let uu____2581 =
                      let uu____2588 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____2588] in
                    closures_as_binders_delayed cfg env uu____2581 in
                  (match uu____2568 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____2610 =
                         let uu____2611 =
                           let uu____2618 =
                             let uu____2619 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____2619
                               FStar_Pervasives_Native.fst in
                           (uu____2618, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____2611 in
                       mk uu____2610 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____2710 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____2710
                    | FStar_Util.Inr c ->
                        let uu____2724 = close_comp cfg env c in
                        FStar_Util.Inr uu____2724 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____2740 =
                    let uu____2741 =
                      let uu____2768 = closure_as_term_delayed cfg env t11 in
                      (uu____2768, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____2741 in
                  mk uu____2740 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____2819 =
                    let uu____2820 =
                      let uu____2827 = closure_as_term_delayed cfg env t' in
                      let uu____2830 =
                        let uu____2831 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____2831 in
                      (uu____2827, uu____2830) in
                    FStar_Syntax_Syntax.Tm_meta uu____2820 in
                  mk uu____2819 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____2891 =
                    let uu____2892 =
                      let uu____2899 = closure_as_term_delayed cfg env t' in
                      let uu____2902 =
                        let uu____2903 =
                          let uu____2910 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____2910) in
                        FStar_Syntax_Syntax.Meta_monadic uu____2903 in
                      (uu____2899, uu____2902) in
                    FStar_Syntax_Syntax.Tm_meta uu____2892 in
                  mk uu____2891 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____2929 =
                    let uu____2930 =
                      let uu____2937 = closure_as_term_delayed cfg env t' in
                      let uu____2940 =
                        let uu____2941 =
                          let uu____2950 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____2950) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____2941 in
                      (uu____2937, uu____2940) in
                    FStar_Syntax_Syntax.Tm_meta uu____2930 in
                  mk uu____2929 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____2963 =
                    let uu____2964 =
                      let uu____2971 = closure_as_term_delayed cfg env t' in
                      (uu____2971, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____2964 in
                  mk uu____2963 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____3001  -> Dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let uu____3008 =
                    let uu____3019 = FStar_Syntax_Syntax.is_top_level [lb] in
                    if uu____3019
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       let uu____3038 =
                         closure_as_term cfg (Dummy :: env0) body in
                       ((FStar_Util.Inl
                           (let uu___188_3044 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___188_3044.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___188_3044.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____3038)) in
                  (match uu____3008 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___189_3060 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___189_3060.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___189_3060.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         } in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____3071,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____3106  -> fun env2  -> Dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____3113 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____3113
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____3121  -> fun env2  -> Dummy :: env2) lbs
                          env_univs in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let nm =
                      let uu____3131 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____3131
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         FStar_All.pipe_right
                           (let uu___190_3143 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___190_3143.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___190_3143.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_43  -> FStar_Util.Inl _0_43)) in
                    let uu___191_3144 = lb in
                    let uu____3145 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___191_3144.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___191_3144.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____3145
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____3163  -> fun env1  -> Dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____3242 =
                    match uu____3242 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____3307 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____3330 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____3396  ->
                                        fun uu____3397  ->
                                          match (uu____3396, uu____3397) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____3500 =
                                                norm_pat env3 p1 in
                                              (match uu____3500 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____3330 with
                               | (pats1,env3) ->
                                   ((let uu___192_3602 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___192_3602.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___193_3621 = x in
                                let uu____3622 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___193_3621.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___193_3621.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3622
                                } in
                              ((let uu___194_3630 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___194_3630.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___195_3635 = x in
                                let uu____3636 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___195_3635.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___195_3635.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3636
                                } in
                              ((let uu___196_3644 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___196_3644.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___197_3654 = x in
                                let uu____3655 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___197_3654.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___197_3654.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3655
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___198_3664 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___198_3664.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____3667 = norm_pat env1 pat in
                        (match uu____3667 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3702 =
                                     closure_as_term cfg env2 w in
                                   FStar_Pervasives_Native.Some uu____3702 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____3708 =
                    let uu____3709 =
                      let uu____3732 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____3732) in
                    FStar_Syntax_Syntax.Tm_match uu____3709 in
                  mk uu____3708 t1.FStar_Syntax_Syntax.pos))
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
        | uu____3814 -> closure_as_term cfg env t
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
        | uu____3838 ->
            FStar_List.map
              (fun uu____3857  ->
                 match uu____3857 with
                 | (x,imp) ->
                     let uu____3876 = closure_as_term_delayed cfg env x in
                     (uu____3876, imp)) args
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
        let uu____3892 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____3947  ->
                  fun uu____3948  ->
                    match (uu____3947, uu____3948) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___199_4030 = b in
                          let uu____4031 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___199_4030.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___199_4030.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____4031
                          } in
                        let env2 = Dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____3892 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____4112 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____4127 = closure_as_term_delayed cfg env t in
                 let uu____4128 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____4127 uu____4128
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____4141 = closure_as_term_delayed cfg env t in
                 let uu____4142 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____4141 uu____4142
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
                        (fun uu___170_4168  ->
                           match uu___170_4168 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____4172 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____4172
                           | f -> f)) in
                 let uu____4176 =
                   let uu___200_4177 = c1 in
                   let uu____4178 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____4178;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___200_4177.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____4176)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags  ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___171_4188  ->
            match uu___171_4188 with
            | FStar_Syntax_Syntax.DECREASES uu____4189 -> false
            | uu____4192 -> true))
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
                   (fun uu___172_4212  ->
                      match uu___172_4212 with
                      | FStar_Syntax_Syntax.DECREASES uu____4213 -> false
                      | uu____4216 -> true)) in
            let rc1 =
              let uu___201_4218 = rc in
              let uu____4219 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___201_4218.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____4219;
                FStar_Syntax_Syntax.residual_flags = flags
              } in
            FStar_Pervasives_Native.Some rc1
        | uu____4226 -> lopt
let built_in_primitive_steps: primitive_step Prims.list =
  let const_as_tm c p = mk (FStar_Syntax_Syntax.Tm_constant c) p in
  let int_as_const p i =
    let uu____4247 =
      let uu____4248 =
        let uu____4259 = FStar_Util.string_of_int i in
        (uu____4259, FStar_Pervasives_Native.None) in
      FStar_Const.Const_int uu____4248 in
    const_as_tm uu____4247 p in
  let bool_as_const p b = const_as_tm (FStar_Const.Const_bool b) p in
  let string_as_const p b = const_as_tm (FStar_Const.Const_string (b, p)) p in
  let arg_as_int uu____4293 =
    match uu____4293 with
    | (a,uu____4301) ->
        let uu____4304 =
          let uu____4305 = FStar_Syntax_Subst.compress a in
          uu____4305.FStar_Syntax_Syntax.n in
        (match uu____4304 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (i,FStar_Pervasives_Native.None )) ->
             let uu____4321 = FStar_Util.int_of_string i in
             FStar_Pervasives_Native.Some uu____4321
         | uu____4322 -> FStar_Pervasives_Native.None) in
  let arg_as_bounded_int uu____4336 =
    match uu____4336 with
    | (a,uu____4348) ->
        let uu____4355 =
          let uu____4356 = FStar_Syntax_Subst.compress a in
          uu____4356.FStar_Syntax_Syntax.n in
        (match uu____4355 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____4366;
                FStar_Syntax_Syntax.vars = uu____4367;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____4369;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____4370;_},uu____4371)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____4410 =
               let uu____4415 = FStar_Util.int_of_string i in
               (fv1, uu____4415) in
             FStar_Pervasives_Native.Some uu____4410
         | uu____4420 -> FStar_Pervasives_Native.None) in
  let arg_as_bool uu____4434 =
    match uu____4434 with
    | (a,uu____4442) ->
        let uu____4445 =
          let uu____4446 = FStar_Syntax_Subst.compress a in
          uu____4446.FStar_Syntax_Syntax.n in
        (match uu____4445 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
             FStar_Pervasives_Native.Some b
         | uu____4452 -> FStar_Pervasives_Native.None) in
  let arg_as_char uu____4462 =
    match uu____4462 with
    | (a,uu____4470) ->
        let uu____4473 =
          let uu____4474 = FStar_Syntax_Subst.compress a in
          uu____4474.FStar_Syntax_Syntax.n in
        (match uu____4473 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
             FStar_Pervasives_Native.Some c
         | uu____4480 -> FStar_Pervasives_Native.None) in
  let arg_as_string uu____4490 =
    match uu____4490 with
    | (a,uu____4498) ->
        let uu____4501 =
          let uu____4502 = FStar_Syntax_Subst.compress a in
          uu____4502.FStar_Syntax_Syntax.n in
        (match uu____4501 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____4508)) -> FStar_Pervasives_Native.Some s
         | uu____4509 -> FStar_Pervasives_Native.None) in
  let arg_as_list f uu____4535 =
    match uu____4535 with
    | (a,uu____4549) ->
        let rec sequence l =
          match l with
          | [] -> FStar_Pervasives_Native.Some []
          | (FStar_Pervasives_Native.None )::uu____4578 ->
              FStar_Pervasives_Native.None
          | (FStar_Pervasives_Native.Some x)::xs ->
              let uu____4595 = sequence xs in
              (match uu____4595 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some xs' ->
                   FStar_Pervasives_Native.Some (x :: xs')) in
        let uu____4615 = FStar_Syntax_Util.list_elements a in
        (match uu____4615 with
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some elts ->
             let uu____4633 =
               FStar_List.map
                 (fun x  ->
                    let uu____4643 = FStar_Syntax_Syntax.as_arg x in
                    f uu____4643) elts in
             sequence uu____4633) in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4681 = f a in FStar_Pervasives_Native.Some uu____4681
    | uu____4682 -> FStar_Pervasives_Native.None in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4732 = f a0 a1 in FStar_Pervasives_Native.Some uu____4732
    | uu____4733 -> FStar_Pervasives_Native.None in
  let unary_op as_a f r args =
    let uu____4782 = FStar_List.map as_a args in lift_unary (f r) uu____4782 in
  let binary_op as_a f r args =
    let uu____4838 = FStar_List.map as_a args in lift_binary (f r) uu____4838 in
  let as_primitive_step uu____4862 =
    match uu____4862 with
    | (l,arity,f) ->
        { name = l; arity; strong_reduction_ok = true; interpretation = f } in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  -> fun x  -> let uu____4910 = f x in int_as_const r uu____4910) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  -> let uu____4938 = f x y in int_as_const r uu____4938) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  -> fun x  -> let uu____4959 = f x in bool_as_const r uu____4959) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  -> let uu____4987 = f x y in bool_as_const r uu____4987) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  -> let uu____5015 = f x y in string_as_const r uu____5015) in
  let list_of_string' rng s =
    let name l =
      let uu____5029 =
        let uu____5030 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____5030 in
      mk uu____5029 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____5040 =
      let uu____5043 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____5043 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____5040 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in int_as_const rng r in
  let string_concat' rng args =
    match args with
    | a1::a2::[] ->
        let uu____5118 = arg_as_string a1 in
        (match uu____5118 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5124 = arg_as_list arg_as_string a2 in
             (match uu____5124 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____5137 = string_as_const rng r in
                  FStar_Pervasives_Native.Some uu____5137
              | uu____5138 -> FStar_Pervasives_Native.None)
         | uu____5143 -> FStar_Pervasives_Native.None)
    | uu____5146 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____5160 = FStar_Util.string_of_int i in
    string_as_const rng uu____5160 in
  let string_of_bool1 rng b =
    string_as_const rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____5176 = FStar_Util.string_of_int i in
    string_as_const rng uu____5176 in
  let string_of_bool2 rng b =
    string_as_const rng (if b then "true" else "false") in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r in
  let range_of1 uu____5206 args =
    match args with
    | uu____5218::(t,uu____5220)::[] ->
        let uu____5249 = term_of_range t.FStar_Syntax_Syntax.pos in
        FStar_Pervasives_Native.Some uu____5249
    | uu____5254 -> FStar_Pervasives_Native.None in
  let set_range_of1 r args =
    match args with
    | uu____5286::(t,uu____5288)::(r1,uu____5290)::[] ->
        let r2 = FStar_Syntax_Embeddings.unembed_range r1 in
        FStar_Pervasives_Native.Some
          (let uu___202_5315 = t in
           {
             FStar_Syntax_Syntax.n = (uu___202_5315.FStar_Syntax_Syntax.n);
             FStar_Syntax_Syntax.pos = r2;
             FStar_Syntax_Syntax.vars =
               (uu___202_5315.FStar_Syntax_Syntax.vars)
           })
    | uu____5316 -> FStar_Pervasives_Native.None in
  let mk_range1 r args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____5395 =
          let uu____5416 = arg_as_string fn in
          let uu____5419 = arg_as_int from_line in
          let uu____5422 = arg_as_int from_col in
          let uu____5425 = arg_as_int to_line in
          let uu____5428 = arg_as_int to_col in
          (uu____5416, uu____5419, uu____5422, uu____5425, uu____5428) in
        (match uu____5395 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r1 =
               let uu____5459 = FStar_Range.mk_pos from_l from_c in
               let uu____5460 = FStar_Range.mk_pos to_l to_c in
               FStar_Range.mk_range fn1 uu____5459 uu____5460 in
             let uu____5461 = term_of_range r1 in
             FStar_Pervasives_Native.Some uu____5461
         | uu____5466 -> FStar_Pervasives_Native.None)
    | uu____5487 -> FStar_Pervasives_Native.None in
  let decidable_eq neg rng args =
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) rng in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) rng in
    match args with
    | (_typ,uu____5517)::(a1,uu____5519)::(a2,uu____5521)::[] ->
        let uu____5558 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____5558 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____5571 -> FStar_Pervasives_Native.None)
    | uu____5572 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____5590 =
      let uu____5605 =
        let uu____5620 =
          let uu____5635 =
            let uu____5650 =
              let uu____5665 =
                let uu____5680 =
                  let uu____5695 =
                    let uu____5710 =
                      let uu____5725 =
                        let uu____5740 =
                          let uu____5755 =
                            let uu____5770 =
                              let uu____5785 =
                                let uu____5800 =
                                  let uu____5815 =
                                    let uu____5830 =
                                      let uu____5845 =
                                        let uu____5860 =
                                          let uu____5875 =
                                            let uu____5890 =
                                              let uu____5903 =
                                                FStar_Parser_Const.p2l
                                                  ["FStar";
                                                  "String";
                                                  "list_of_string"] in
                                              (uu____5903,
                                                (Prims.parse_int "1"),
                                                (unary_op arg_as_string
                                                   list_of_string')) in
                                            let uu____5910 =
                                              let uu____5925 =
                                                let uu____5938 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "string_of_list"] in
                                                (uu____5938,
                                                  (Prims.parse_int "1"),
                                                  (unary_op
                                                     (arg_as_list arg_as_char)
                                                     string_of_list')) in
                                              let uu____5947 =
                                                let uu____5962 =
                                                  let uu____5981 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "concat"] in
                                                  (uu____5981,
                                                    (Prims.parse_int "2"),
                                                    string_concat') in
                                                let uu____5994 =
                                                  let uu____6015 =
                                                    let uu____6036 =
                                                      FStar_Parser_Const.p2l
                                                        ["Prims"; "range_of"] in
                                                    (uu____6036,
                                                      (Prims.parse_int "2"),
                                                      range_of1) in
                                                  let uu____6051 =
                                                    let uu____6074 =
                                                      let uu____6093 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "set_range_of"] in
                                                      (uu____6093,
                                                        (Prims.parse_int "3"),
                                                        set_range_of1) in
                                                    let uu____6106 =
                                                      let uu____6127 =
                                                        let uu____6146 =
                                                          FStar_Parser_Const.p2l
                                                            ["Prims";
                                                            "mk_range"] in
                                                        (uu____6146,
                                                          (Prims.parse_int
                                                             "5"), mk_range1) in
                                                      [uu____6127] in
                                                    uu____6074 :: uu____6106 in
                                                  uu____6015 :: uu____6051 in
                                                uu____5962 :: uu____5994 in
                                              uu____5925 :: uu____5947 in
                                            uu____5890 :: uu____5910 in
                                          (FStar_Parser_Const.op_notEq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq true)) ::
                                            uu____5875 in
                                        (FStar_Parser_Const.op_Eq,
                                          (Prims.parse_int "3"),
                                          (decidable_eq false)) :: uu____5860 in
                                      (FStar_Parser_Const.string_compare,
                                        (Prims.parse_int "2"),
                                        (binary_op arg_as_string
                                           string_compare'))
                                        :: uu____5845 in
                                    (FStar_Parser_Const.string_of_bool_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_bool string_of_bool2))
                                      :: uu____5830 in
                                  (FStar_Parser_Const.string_of_int_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_int string_of_int2)) ::
                                    uu____5815 in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____5800 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5785 in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____5770 in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____5755 in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____5740 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____5725 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
                      :: uu____5710 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____5695 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____5680 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____5665 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____5650 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____5635 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____5620 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____5605 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____5590 in
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
      let uu____6751 =
        let uu____6752 =
          let uu____6753 = FStar_Syntax_Syntax.as_arg c in [uu____6753] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6752 in
      uu____6751 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____6788 =
              let uu____6801 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____6801, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____6820  ->
                        fun uu____6821  ->
                          match (uu____6820, uu____6821) with
                          | ((int_to_t1,x),(uu____6840,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____6850 =
              let uu____6865 =
                let uu____6878 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____6878, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____6897  ->
                          fun uu____6898  ->
                            match (uu____6897, uu____6898) with
                            | ((int_to_t1,x),(uu____6917,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____6927 =
                let uu____6942 =
                  let uu____6955 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____6955, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____6974  ->
                            fun uu____6975  ->
                              match (uu____6974, uu____6975) with
                              | ((int_to_t1,x),(uu____6994,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____6942] in
              uu____6865 :: uu____6927 in
            uu____6788 :: uu____6850)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop r args =
    match args with
    | (_typ,uu____7090)::(a1,uu____7092)::(a2,uu____7094)::[] ->
        let uu____7131 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____7131 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___203_7137 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___203_7137.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___203_7137.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___204_7141 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___204_7141.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___204_7141.FStar_Syntax_Syntax.vars)
                })
         | uu____7142 -> FStar_Pervasives_Native.None)
    | (_typ,uu____7144)::uu____7145::(a1,uu____7147)::(a2,uu____7149)::[] ->
        let uu____7198 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____7198 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___203_7204 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___203_7204.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___203_7204.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___204_7208 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___204_7208.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___204_7208.FStar_Syntax_Syntax.vars)
                })
         | uu____7209 -> FStar_Pervasives_Native.None)
    | uu____7210 -> failwith "Unexpected number of arguments" in
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
      let uu____7223 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops cfg.steps) in
      if uu____7223
      then tm
      else
        (let uu____7225 = FStar_Syntax_Util.head_and_args tm in
         match uu____7225 with
         | (head1,args) ->
             let uu____7262 =
               let uu____7263 = FStar_Syntax_Util.un_uinst head1 in
               uu____7263.FStar_Syntax_Syntax.n in
             (match uu____7262 with
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____7267 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps in
                  (match uu____7267 with
                   | FStar_Pervasives_Native.None  -> tm
                   | FStar_Pervasives_Native.Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then
                         (log cfg
                            (fun uu____7284  ->
                               let uu____7285 =
                                 FStar_Syntax_Print.lid_to_string
                                   prim_step.name in
                               let uu____7286 =
                                 FStar_Util.string_of_int
                                   (FStar_List.length args) in
                               let uu____7293 =
                                 FStar_Util.string_of_int prim_step.arity in
                               FStar_Util.print3
                                 "primop: found partially applied %s (%s/%s args)\n"
                                 uu____7285 uu____7286 uu____7293);
                          tm)
                       else
                         (log cfg
                            (fun uu____7298  ->
                               let uu____7299 =
                                 FStar_Syntax_Print.term_to_string tm in
                               FStar_Util.print1
                                 "primop: trying to reduce <%s>\n" uu____7299);
                          (let uu____7300 =
                             prim_step.interpretation
                               head1.FStar_Syntax_Syntax.pos args in
                           match uu____7300 with
                           | FStar_Pervasives_Native.None  ->
                               (log cfg
                                  (fun uu____7306  ->
                                     let uu____7307 =
                                       FStar_Syntax_Print.term_to_string tm in
                                     FStar_Util.print1
                                       "primop: <%s> did not reduce\n"
                                       uu____7307);
                                tm)
                           | FStar_Pervasives_Native.Some reduced ->
                               (log cfg
                                  (fun uu____7313  ->
                                     let uu____7314 =
                                       FStar_Syntax_Print.term_to_string tm in
                                     let uu____7315 =
                                       FStar_Syntax_Print.term_to_string
                                         reduced in
                                     FStar_Util.print2
                                       "primop: <%s> reduced to <%s>\n"
                                       uu____7314 uu____7315);
                                reduced))))
              | uu____7316 -> tm))
let reduce_equality:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___205_7327 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___205_7327.tcenv);
           delta_level = (uu___205_7327.delta_level);
           primitive_steps = equality_ops
         }) tm
let maybe_simplify:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      let tm1 = reduce_primops cfg tm in
      let uu____7337 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify cfg.steps) in
      if uu____7337
      then tm1
      else
        (let w t =
           let uu___206_7349 = t in
           {
             FStar_Syntax_Syntax.n = (uu___206_7349.FStar_Syntax_Syntax.n);
             FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
             FStar_Syntax_Syntax.vars =
               (uu___206_7349.FStar_Syntax_Syntax.vars)
           } in
         let simp_t t =
           match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
               -> FStar_Pervasives_Native.Some true
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
               -> FStar_Pervasives_Native.Some false
           | uu____7366 -> FStar_Pervasives_Native.None in
         let simplify1 arg =
           ((simp_t (FStar_Pervasives_Native.fst arg)), arg) in
         match tm1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.pos = uu____7406;
                     FStar_Syntax_Syntax.vars = uu____7407;_},uu____7408);
                FStar_Syntax_Syntax.pos = uu____7409;
                FStar_Syntax_Syntax.vars = uu____7410;_},args)
             ->
             let uu____7436 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
             if uu____7436
             then
               let uu____7437 =
                 FStar_All.pipe_right args (FStar_List.map simplify1) in
               (match uu____7437 with
                | (FStar_Pervasives_Native.Some (true ),uu____7492)::
                    (uu____7493,(arg,uu____7495))::[] -> arg
                | (uu____7560,(arg,uu____7562))::(FStar_Pervasives_Native.Some
                                                  (true ),uu____7563)::[]
                    -> arg
                | (FStar_Pervasives_Native.Some (false ),uu____7628)::uu____7629::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____7692::(FStar_Pervasives_Native.Some (false
                               ),uu____7693)::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____7756 -> tm1)
             else
               (let uu____7772 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
                if uu____7772
                then
                  let uu____7773 =
                    FStar_All.pipe_right args (FStar_List.map simplify1) in
                  match uu____7773 with
                  | (FStar_Pervasives_Native.Some (true ),uu____7828)::uu____7829::[]
                      -> w FStar_Syntax_Util.t_true
                  | uu____7892::(FStar_Pervasives_Native.Some (true
                                 ),uu____7893)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____7956)::
                      (uu____7957,(arg,uu____7959))::[] -> arg
                  | (uu____8024,(arg,uu____8026))::(FStar_Pervasives_Native.Some
                                                    (false ),uu____8027)::[]
                      -> arg
                  | uu____8092 -> tm1
                else
                  (let uu____8108 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.imp_lid in
                   if uu____8108
                   then
                     let uu____8109 =
                       FStar_All.pipe_right args (FStar_List.map simplify1) in
                     match uu____8109 with
                     | uu____8164::(FStar_Pervasives_Native.Some (true
                                    ),uu____8165)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____8228)::uu____8229::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____8292)::
                         (uu____8293,(arg,uu____8295))::[] -> arg
                     | (uu____8360,(p,uu____8362))::(uu____8363,(q,uu____8365))::[]
                         ->
                         let uu____8430 = FStar_Syntax_Util.term_eq p q in
                         (if uu____8430
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____8432 -> tm1
                   else
                     (let uu____8448 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____8448
                      then
                        let uu____8449 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1) in
                        match uu____8449 with
                        | (FStar_Pervasives_Native.Some (true ),uu____8504)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____8543)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____8582 -> tm1
                      else
                        (let uu____8598 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____8598
                         then
                           match args with
                           | (t,uu____8600)::[] ->
                               let uu____8617 =
                                 let uu____8618 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____8618.FStar_Syntax_Syntax.n in
                               (match uu____8617 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____8621::[],body,uu____8623) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____8650 -> tm1)
                                | uu____8653 -> tm1)
                           | (uu____8654,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____8655))::
                               (t,uu____8657)::[] ->
                               let uu____8696 =
                                 let uu____8697 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____8697.FStar_Syntax_Syntax.n in
                               (match uu____8696 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____8700::[],body,uu____8702) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____8729 -> tm1)
                                | uu____8732 -> tm1)
                           | uu____8733 -> tm1
                         else
                           (let uu____8743 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____8743
                            then
                              match args with
                              | (t,uu____8745)::[] ->
                                  let uu____8762 =
                                    let uu____8763 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____8763.FStar_Syntax_Syntax.n in
                                  (match uu____8762 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____8766::[],body,uu____8768) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____8795 -> tm1)
                                   | uu____8798 -> tm1)
                              | (uu____8799,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____8800))::
                                  (t,uu____8802)::[] ->
                                  let uu____8841 =
                                    let uu____8842 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____8842.FStar_Syntax_Syntax.n in
                                  (match uu____8841 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____8845::[],body,uu____8847) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____8874 -> tm1)
                                   | uu____8877 -> tm1)
                              | uu____8878 -> tm1
                            else reduce_equality cfg tm1)))))
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                FStar_Syntax_Syntax.pos = uu____8889;
                FStar_Syntax_Syntax.vars = uu____8890;_},args)
             ->
             let uu____8912 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
             if uu____8912
             then
               let uu____8913 =
                 FStar_All.pipe_right args (FStar_List.map simplify1) in
               (match uu____8913 with
                | (FStar_Pervasives_Native.Some (true ),uu____8968)::
                    (uu____8969,(arg,uu____8971))::[] -> arg
                | (uu____9036,(arg,uu____9038))::(FStar_Pervasives_Native.Some
                                                  (true ),uu____9039)::[]
                    -> arg
                | (FStar_Pervasives_Native.Some (false ),uu____9104)::uu____9105::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____9168::(FStar_Pervasives_Native.Some (false
                               ),uu____9169)::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____9232 -> tm1)
             else
               (let uu____9248 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
                if uu____9248
                then
                  let uu____9249 =
                    FStar_All.pipe_right args (FStar_List.map simplify1) in
                  match uu____9249 with
                  | (FStar_Pervasives_Native.Some (true ),uu____9304)::uu____9305::[]
                      -> w FStar_Syntax_Util.t_true
                  | uu____9368::(FStar_Pervasives_Native.Some (true
                                 ),uu____9369)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____9432)::
                      (uu____9433,(arg,uu____9435))::[] -> arg
                  | (uu____9500,(arg,uu____9502))::(FStar_Pervasives_Native.Some
                                                    (false ),uu____9503)::[]
                      -> arg
                  | uu____9568 -> tm1
                else
                  (let uu____9584 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.imp_lid in
                   if uu____9584
                   then
                     let uu____9585 =
                       FStar_All.pipe_right args (FStar_List.map simplify1) in
                     match uu____9585 with
                     | uu____9640::(FStar_Pervasives_Native.Some (true
                                    ),uu____9641)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____9704)::uu____9705::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____9768)::
                         (uu____9769,(arg,uu____9771))::[] -> arg
                     | (uu____9836,(p,uu____9838))::(uu____9839,(q,uu____9841))::[]
                         ->
                         let uu____9906 = FStar_Syntax_Util.term_eq p q in
                         (if uu____9906
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____9908 -> tm1
                   else
                     (let uu____9924 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____9924
                      then
                        let uu____9925 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1) in
                        match uu____9925 with
                        | (FStar_Pervasives_Native.Some (true ),uu____9980)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____10019)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____10058 -> tm1
                      else
                        (let uu____10074 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____10074
                         then
                           match args with
                           | (t,uu____10076)::[] ->
                               let uu____10093 =
                                 let uu____10094 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____10094.FStar_Syntax_Syntax.n in
                               (match uu____10093 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____10097::[],body,uu____10099) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____10126 -> tm1)
                                | uu____10129 -> tm1)
                           | (uu____10130,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____10131))::
                               (t,uu____10133)::[] ->
                               let uu____10172 =
                                 let uu____10173 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____10173.FStar_Syntax_Syntax.n in
                               (match uu____10172 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____10176::[],body,uu____10178) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____10205 -> tm1)
                                | uu____10208 -> tm1)
                           | uu____10209 -> tm1
                         else
                           (let uu____10219 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____10219
                            then
                              match args with
                              | (t,uu____10221)::[] ->
                                  let uu____10238 =
                                    let uu____10239 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____10239.FStar_Syntax_Syntax.n in
                                  (match uu____10238 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____10242::[],body,uu____10244) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____10271 -> tm1)
                                   | uu____10274 -> tm1)
                              | (uu____10275,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____10276))::
                                  (t,uu____10278)::[] ->
                                  let uu____10317 =
                                    let uu____10318 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____10318.FStar_Syntax_Syntax.n in
                                  (match uu____10317 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____10321::[],body,uu____10323) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____10350 -> tm1)
                                   | uu____10353 -> tm1)
                              | uu____10354 -> tm1
                            else reduce_equality cfg tm1)))))
         | uu____10364 -> tm1)
let is_norm_request:
  'Auu____10371 .
    FStar_Syntax_Syntax.term -> 'Auu____10371 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10384 =
        let uu____10391 =
          let uu____10392 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10392.FStar_Syntax_Syntax.n in
        (uu____10391, args) in
      match uu____10384 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10398::uu____10399::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10403::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10408::uu____10409::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10412 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___173_10424  ->
    match uu___173_10424 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.WHNF  -> [WHNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10430 =
          let uu____10433 =
            let uu____10434 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____10434 in
          [uu____10433] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10430
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____10453 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10453) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10491 =
          FStar_Syntax_Embeddings.unembed_list
            FStar_Syntax_Embeddings.unembed_norm_step s in
        FStar_All.pipe_left tr_norm_steps uu____10491 in
      match args with
      | uu____10504::(tm,uu____10506)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____10529)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____10544)::uu____10545::(tm,uu____10547)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____10587 =
              let uu____10590 = full_norm steps in parse_steps uu____10590 in
            Beta :: uu____10587 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____10599 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___174_10617  ->
    match uu___174_10617 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.pos = uu____10620;
           FStar_Syntax_Syntax.vars = uu____10621;_},uu____10622,uu____10623))::uu____10624
        -> true
    | uu____10631 -> false
let should_reify: cfg -> stack_elt Prims.list -> Prims.bool =
  fun cfg  ->
    fun stack1  ->
      match stack1 with
      | (App
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify );
             FStar_Syntax_Syntax.pos = uu____10646;
             FStar_Syntax_Syntax.vars = uu____10647;_},uu____10648,uu____10649))::uu____10650
          -> FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)
      | uu____10657 -> false
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
            (fun uu____10792  ->
               let uu____10793 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____10794 = FStar_Syntax_Print.term_to_string t1 in
               let uu____10795 =
                 let uu____10796 =
                   let uu____10799 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____10799 in
                 stack_to_string uu____10796 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____10793
                 uu____10794 uu____10795);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____10822 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____10847 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____10864 =
                 let uu____10865 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____10866 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____10865 uu____10866 in
               failwith uu____10864
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____10867 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____10884 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____10885 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10886;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____10887;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10890;
                 FStar_Syntax_Syntax.fv_delta = uu____10891;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10892;
                 FStar_Syntax_Syntax.fv_delta = uu____10893;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____10894);_}
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
                 let uu___207_10936 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___207_10936.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___207_10936.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____10969 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____10969) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___208_10977 = cfg in
                 let uu____10978 =
                   FStar_List.filter
                     (fun uu___175_10981  ->
                        match uu___175_10981 with
                        | UnfoldOnly uu____10982 -> false
                        | NoDeltaSteps  -> false
                        | uu____10985 -> true) cfg.steps in
                 {
                   steps = uu____10978;
                   tcenv = (uu___208_10977.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___208_10977.primitive_steps)
                 } in
               let uu____10986 = get_norm_request (norm cfg' env []) args in
               (match uu____10986 with
                | (s,tm) ->
                    let delta_level =
                      let uu____11002 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___176_11007  ->
                                match uu___176_11007 with
                                | UnfoldUntil uu____11008 -> true
                                | UnfoldOnly uu____11009 -> true
                                | uu____11012 -> false)) in
                      if uu____11002
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___209_11017 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___209_11017.tcenv);
                        delta_level;
                        primitive_steps = (uu___209_11017.primitive_steps)
                      } in
                    let stack' =
                      let tail1 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let uu____11028 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____11028
                      then
                        let uu____11031 =
                          let uu____11032 =
                            let uu____11037 = FStar_Util.now () in
                            (t1, uu____11037) in
                          Debug uu____11032 in
                        uu____11031 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11039;
                  FStar_Syntax_Syntax.vars = uu____11040;_},a1::a2::rest)
               ->
               let uu____11088 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11088 with
                | (hd1,uu____11104) ->
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
                    (FStar_Const.Const_reflect uu____11169);
                  FStar_Syntax_Syntax.pos = uu____11170;
                  FStar_Syntax_Syntax.vars = uu____11171;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____11203 = FStar_List.tl stack1 in
               norm cfg env uu____11203 (FStar_Pervasives_Native.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11206;
                  FStar_Syntax_Syntax.vars = uu____11207;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____11239 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11239 with
                | (reify_head,uu____11255) ->
                    let a1 =
                      let uu____11277 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (FStar_Pervasives_Native.fst a) in
                      FStar_Syntax_Subst.compress uu____11277 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____11280);
                            FStar_Syntax_Syntax.pos = uu____11281;
                            FStar_Syntax_Syntax.vars = uu____11282;_},a2::[])
                         ->
                         norm cfg env stack1 (FStar_Pervasives_Native.fst a2)
                     | uu____11316 ->
                         let stack2 =
                           (App
                              (reify_head, FStar_Pervasives_Native.None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11326 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____11326
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11333 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11333
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____11336 =
                      let uu____11343 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11343, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11336 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___177_11357  ->
                         match uu___177_11357 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11360 =
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
                 if uu____11360
                 then false
                 else
                   (let uu____11362 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___178_11369  ->
                              match uu___178_11369 with
                              | UnfoldOnly uu____11370 -> true
                              | uu____11373 -> false)) in
                    match uu____11362 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11377 -> should_delta) in
               (log cfg
                  (fun uu____11385  ->
                     let uu____11386 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11387 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____11388 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11386 uu____11387 uu____11388);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack1 t1
                else
                  (let r_env =
                     let uu____11391 = FStar_Syntax_Syntax.range_of_fv f in
                     FStar_TypeChecker_Env.set_range cfg.tcenv uu____11391 in
                   let uu____11392 =
                     FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                       r_env
                       (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   match uu____11392 with
                   | FStar_Pervasives_Native.None  ->
                       (log cfg
                          (fun uu____11405  ->
                             FStar_Util.print "Tm_fvar case 2\n" []);
                        rebuild cfg env stack1 t1)
                   | FStar_Pervasives_Native.Some (us,t2) ->
                       (log cfg
                          (fun uu____11416  ->
                             let uu____11417 =
                               FStar_Syntax_Print.term_to_string t0 in
                             let uu____11418 =
                               FStar_Syntax_Print.term_to_string t2 in
                             FStar_Util.print2 ">>> Unfolded %s to %s\n"
                               uu____11417 uu____11418);
                        (let t3 =
                           let uu____11420 =
                             FStar_All.pipe_right cfg.steps
                               (FStar_List.contains
                                  (UnfoldUntil
                                     FStar_Syntax_Syntax.Delta_constant)) in
                           if uu____11420
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
                           | (UnivArgs (us',uu____11430))::stack2 ->
                               let env1 =
                                 FStar_All.pipe_right us'
                                   (FStar_List.fold_left
                                      (fun env1  ->
                                         fun u  -> (Univ u) :: env1) env) in
                               norm cfg env1 stack2 t3
                           | uu____11453 when
                               FStar_All.pipe_right cfg.steps
                                 (FStar_List.contains EraseUniverses)
                               -> norm cfg env stack1 t3
                           | uu____11454 ->
                               let uu____11455 =
                                 let uu____11456 =
                                   FStar_Syntax_Print.lid_to_string
                                     (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                 FStar_Util.format1
                                   "Impossible: missing universe instantiation on %s"
                                   uu____11456 in
                               failwith uu____11455
                         else norm cfg env stack1 t3))))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11459 = lookup_bvar env x in
               (match uu____11459 with
                | Univ uu____11460 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11485 = FStar_ST.op_Bang r in
                      (match uu____11485 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11586  ->
                                 let uu____11587 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____11588 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11587
                                   uu____11588);
                            (let uu____11589 =
                               let uu____11590 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____11590.FStar_Syntax_Syntax.n in
                             match uu____11589 with
                             | FStar_Syntax_Syntax.Tm_abs uu____11593 ->
                                 norm cfg env2 stack1 t'
                             | uu____11610 -> rebuild cfg env2 stack1 t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____11662)::uu____11663 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11672)::uu____11673 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11683,uu____11684))::stack_rest ->
                    (match c with
                     | Univ uu____11688 -> norm cfg (c :: env) stack_rest t1
                     | uu____11689 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____11694::[] ->
                              (log cfg
                                 (fun uu____11710  ->
                                    let uu____11711 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11711);
                               norm cfg (c :: env) stack_rest body)
                          | uu____11712::tl1 ->
                              (log cfg
                                 (fun uu____11731  ->
                                    let uu____11732 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11732);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___210_11762 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___210_11762.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____11847  ->
                          let uu____11848 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11848);
                     norm cfg env stack2 t1)
                | (Debug uu____11849)::uu____11850 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11857 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11857
                    else
                      (let uu____11859 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11859 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11883  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11899 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11899
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11909 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11909)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___211_11914 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___211_11914.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___211_11914.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11915 -> lopt in
                           (log cfg
                              (fun uu____11921  ->
                                 let uu____11922 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11922);
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
                | (Meta uu____11939)::uu____11940 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11947 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11947
                    else
                      (let uu____11949 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11949 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11973  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11989 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11989
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11999 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11999)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___211_12004 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___211_12004.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___211_12004.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12005 -> lopt in
                           (log cfg
                              (fun uu____12011  ->
                                 let uu____12012 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12012);
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
                | (Let uu____12029)::uu____12030 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12041 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12041
                    else
                      (let uu____12043 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12043 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12067  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12083 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12083
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12093 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12093)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___211_12098 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___211_12098.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___211_12098.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12099 -> lopt in
                           (log cfg
                              (fun uu____12105  ->
                                 let uu____12106 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12106);
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
                | (App uu____12123)::uu____12124 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12133 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12133
                    else
                      (let uu____12135 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12135 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12159  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12175 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12175
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12185 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12185)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___211_12190 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___211_12190.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___211_12190.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12191 -> lopt in
                           (log cfg
                              (fun uu____12197  ->
                                 let uu____12198 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12198);
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
                | (Abs uu____12215)::uu____12216 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12231 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12231
                    else
                      (let uu____12233 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12233 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12257  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12273 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12273
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12283 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12283)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___211_12288 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___211_12288.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___211_12288.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12289 -> lopt in
                           (log cfg
                              (fun uu____12295  ->
                                 let uu____12296 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12296);
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
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12313 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12313
                    else
                      (let uu____12315 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12315 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12339  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12355 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12355
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12365 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12365)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___211_12370 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___211_12370.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___211_12370.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12371 -> lopt in
                           (log cfg
                              (fun uu____12377  ->
                                 let uu____12378 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12378);
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
                      (fun uu____12433  ->
                         fun stack2  ->
                           match uu____12433 with
                           | (a,aq) ->
                               let uu____12445 =
                                 let uu____12446 =
                                   let uu____12453 =
                                     let uu____12454 =
                                       let uu____12473 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____12473, false) in
                                     Clos uu____12454 in
                                   (uu____12453, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____12446 in
                               uu____12445 :: stack2) args) in
               (log cfg
                  (fun uu____12525  ->
                     let uu____12526 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12526);
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
                             ((let uu___212_12550 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___212_12550.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___212_12550.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____12551 ->
                      let uu____12556 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12556)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____12559 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____12559 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____12584 =
                          let uu____12585 =
                            let uu____12592 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___213_12594 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___213_12594.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___213_12594.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12592) in
                          FStar_Syntax_Syntax.Tm_refine uu____12585 in
                        mk uu____12584 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____12613 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____12613
               else
                 (let uu____12615 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____12615 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12623 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12635  -> Dummy :: env1) env) in
                        norm_comp cfg uu____12623 c1 in
                      let t2 =
                        let uu____12645 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____12645 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____12704)::uu____12705 -> norm cfg env stack1 t11
                | (Arg uu____12714)::uu____12715 -> norm cfg env stack1 t11
                | (App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____12724;
                       FStar_Syntax_Syntax.vars = uu____12725;_},uu____12726,uu____12727))::uu____12728
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____12735)::uu____12736 ->
                    norm cfg env stack1 t11
                | uu____12745 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____12749  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____12766 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____12766
                        | FStar_Util.Inr c ->
                            let uu____12774 = norm_comp cfg env c in
                            FStar_Util.Inr uu____12774 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____12780 =
                        let uu____12781 =
                          let uu____12782 =
                            let uu____12809 = FStar_Syntax_Util.unascribe t12 in
                            (uu____12809, (tc1, tacopt1), l) in
                          FStar_Syntax_Syntax.Tm_ascribed uu____12782 in
                        mk uu____12781 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____12780)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____12885,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____12886;
                               FStar_Syntax_Syntax.lbunivs = uu____12887;
                               FStar_Syntax_Syntax.lbtyp = uu____12888;
                               FStar_Syntax_Syntax.lbeff = uu____12889;
                               FStar_Syntax_Syntax.lbdef = uu____12890;_}::uu____12891),uu____12892)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____12928 =
                 (let uu____12931 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____12931) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____12933 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____12933))) in
               if uu____12928
               then
                 let env1 =
                   let uu____12937 =
                     let uu____12938 =
                       let uu____12957 =
                         FStar_Util.mk_ref FStar_Pervasives_Native.None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____12957,
                         false) in
                     Clos uu____12938 in
                   uu____12937 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____13009 =
                    let uu____13014 =
                      let uu____13015 =
                        let uu____13016 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____13016
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____13015] in
                    FStar_Syntax_Subst.open_term uu____13014 body in
                  match uu____13009 with
                  | (bs,body1) ->
                      let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                      let lbname =
                        let x =
                          let uu____13030 = FStar_List.hd bs in
                          FStar_Pervasives_Native.fst uu____13030 in
                        FStar_Util.Inl
                          (let uu___214_13040 = x in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___214_13040.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___214_13040.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = ty
                           }) in
                      let lb1 =
                        let uu___215_13042 = lb in
                        let uu____13043 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = lbname;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___215_13042.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = ty;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___215_13042.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____13043
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____13060  -> Dummy :: env1)
                             env) in
                      let cfg1 = only_strong_steps cfg in
                      norm cfg1 env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let ((true ,lbs),body) when
               (FStar_List.contains CompressUvars cfg.steps) ||
                 ((FStar_List.contains (Exclude Zeta) cfg.steps) &&
                    (FStar_List.contains PureSubtermsWithinComputations
                       cfg.steps))
               ->
               let uu____13084 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____13084 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____13120 =
                               let uu___216_13121 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___216_13121.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___216_13121.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____13120 in
                           let uu____13122 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____13122 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____13142 =
                                   FStar_List.map (fun uu____13146  -> Dummy)
                                     lbs1 in
                                 let uu____13147 =
                                   let uu____13150 =
                                     FStar_List.map
                                       (fun uu____13158  -> Dummy) xs1 in
                                   FStar_List.append uu____13150 env in
                                 FStar_List.append uu____13142 uu____13147 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13170 =
                                       let uu___217_13171 = rc in
                                       let uu____13172 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___217_13171.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13172;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___217_13171.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____13170
                                 | uu____13179 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___218_13183 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___218_13183.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___218_13183.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____13187 =
                        FStar_List.map (fun uu____13191  -> Dummy) lbs2 in
                      FStar_List.append uu____13187 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____13193 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____13193 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___219_13209 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___219_13209.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___219_13209.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____13236 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____13236
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13255 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13306  ->
                        match uu____13306 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____13379 =
                                let uu___220_13380 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___220_13380.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___220_13380.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____13379 in
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
               (match uu____13255 with
                | (rec_env,memos,uu____13508) ->
                    let uu____13537 =
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
                             let uu____14002 =
                               let uu____14003 =
                                 let uu____14022 =
                                   FStar_Util.mk_ref
                                     FStar_Pervasives_Native.None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____14022, false) in
                               Clos uu____14003 in
                             uu____14002 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
                    norm cfg body_env stack1 body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (match m with
                | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                    let uu____14089 =
                      let uu____14090 = should_reify cfg stack1 in
                      Prims.op_Negation uu____14090 in
                    if uu____14089
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____14100 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____14100
                        then
                          let uu___221_14101 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___221_14101.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps =
                              (uu___221_14101.primitive_steps)
                          }
                        else
                          (let uu___222_14103 = cfg in
                           {
                             steps =
                               (FStar_List.append [Exclude Zeta] cfg.steps);
                             tcenv = (uu___222_14103.tcenv);
                             delta_level = (uu___222_14103.delta_level);
                             primitive_steps =
                               (uu___222_14103.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____14105 =
                         let uu____14106 = FStar_Syntax_Subst.compress head1 in
                         uu____14106.FStar_Syntax_Syntax.n in
                       match uu____14105 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____14124 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____14124 with
                            | (uu____14125,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____14131 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____14139 =
                                         let uu____14140 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____14140.FStar_Syntax_Syntax.n in
                                       match uu____14139 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____14146,uu____14147))
                                           ->
                                           let uu____14156 =
                                             let uu____14157 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____14157.FStar_Syntax_Syntax.n in
                                           (match uu____14156 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____14163,msrc,uu____14165))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____14174 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14174
                                            | uu____14175 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____14176 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____14177 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____14177 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___223_14182 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___223_14182.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___223_14182.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___223_14182.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____14183 =
                                            FStar_List.tl stack1 in
                                          let uu____14184 =
                                            let uu____14185 =
                                              let uu____14188 =
                                                let uu____14189 =
                                                  let uu____14202 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____14202) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____14189 in
                                              FStar_Syntax_Syntax.mk
                                                uu____14188 in
                                            uu____14185
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____14183
                                            uu____14184
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____14218 =
                                            let uu____14219 = is_return body in
                                            match uu____14219 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____14223;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____14224;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____14229 -> false in
                                          if uu____14218
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
                                               let uu____14253 =
                                                 let uu____14256 =
                                                   let uu____14257 =
                                                     let uu____14274 =
                                                       let uu____14277 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____14277] in
                                                     (uu____14274, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc)) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____14257 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____14256 in
                                               uu____14253
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____14293 =
                                                 let uu____14294 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____14294.FStar_Syntax_Syntax.n in
                                               match uu____14293 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____14300::uu____14301::[])
                                                   ->
                                                   let uu____14308 =
                                                     let uu____14311 =
                                                       let uu____14312 =
                                                         let uu____14319 =
                                                           let uu____14322 =
                                                             let uu____14323
                                                               =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____14323 in
                                                           let uu____14324 =
                                                             let uu____14327
                                                               =
                                                               let uu____14328
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____14328 in
                                                             [uu____14327] in
                                                           uu____14322 ::
                                                             uu____14324 in
                                                         (bind1, uu____14319) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____14312 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____14311 in
                                                   uu____14308
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____14336 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____14342 =
                                                 let uu____14345 =
                                                   let uu____14346 =
                                                     let uu____14361 =
                                                       let uu____14364 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____14365 =
                                                         let uu____14368 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____14369 =
                                                           let uu____14372 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____14373 =
                                                             let uu____14376
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____14377
                                                               =
                                                               let uu____14380
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____14381
                                                                 =
                                                                 let uu____14384
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____14384] in
                                                               uu____14380 ::
                                                                 uu____14381 in
                                                             uu____14376 ::
                                                               uu____14377 in
                                                           uu____14372 ::
                                                             uu____14373 in
                                                         uu____14368 ::
                                                           uu____14369 in
                                                       uu____14364 ::
                                                         uu____14365 in
                                                     (bind_inst, uu____14361) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____14346 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____14345 in
                                               uu____14342
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____14392 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____14392 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____14416 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____14416 with
                            | (uu____14417,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____14452 =
                                        let uu____14453 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____14453.FStar_Syntax_Syntax.n in
                                      match uu____14452 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____14459) -> t4
                                      | uu____14464 -> head2 in
                                    let uu____14465 =
                                      let uu____14466 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____14466.FStar_Syntax_Syntax.n in
                                    match uu____14465 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____14472 ->
                                        FStar_Pervasives_Native.None in
                                  let uu____14473 = maybe_extract_fv head2 in
                                  match uu____14473 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____14483 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____14483
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____14488 =
                                          maybe_extract_fv head3 in
                                        match uu____14488 with
                                        | FStar_Pervasives_Native.Some
                                            uu____14493 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____14494 ->
                                            FStar_Pervasives_Native.Some
                                              false in
                                      (head3, action_unfolded)
                                  | uu____14499 ->
                                      (head2, FStar_Pervasives_Native.None) in
                                ((let is_arg_impure uu____14514 =
                                    match uu____14514 with
                                    | (e,q) ->
                                        let uu____14521 =
                                          let uu____14522 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____14522.FStar_Syntax_Syntax.n in
                                        (match uu____14521 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____14537 -> false) in
                                  let uu____14538 =
                                    let uu____14539 =
                                      let uu____14546 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____14546 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____14539 in
                                  if uu____14538
                                  then
                                    let uu____14551 =
                                      let uu____14552 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____14552 in
                                    failwith uu____14551
                                  else ());
                                 (let uu____14554 =
                                    maybe_unfold_action head_app in
                                  match uu____14554 with
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
                                      let uu____14593 = FStar_List.tl stack1 in
                                      norm cfg env uu____14593 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____14607 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____14607 in
                           let uu____14608 = FStar_List.tl stack1 in
                           norm cfg env uu____14608 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____14729  ->
                                     match uu____14729 with
                                     | (pat,wopt,tm) ->
                                         let uu____14777 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____14777))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____14809 = FStar_List.tl stack1 in
                           norm cfg env uu____14809 tm
                       | uu____14810 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let uu____14818 = should_reify cfg stack1 in
                    if uu____14818
                    then
                      let uu____14819 = FStar_List.tl stack1 in
                      let uu____14820 =
                        let uu____14821 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____14821 in
                      norm cfg env uu____14819 uu____14820
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____14824 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____14824
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___224_14833 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___224_14833.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___224_14833.primitive_steps)
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
                | uu____14835 ->
                    if FStar_List.contains Unmeta cfg.steps
                    then norm cfg env stack1 head1
                    else
                      (match stack1 with
                       | uu____14837::uu____14838 ->
                           (match m with
                            | FStar_Syntax_Syntax.Meta_labeled
                                (l,r,uu____14843) ->
                                norm cfg env ((Meta (m, r)) :: stack1) head1
                            | FStar_Syntax_Syntax.Meta_alien uu____14844 ->
                                rebuild cfg env stack1 t1
                            | FStar_Syntax_Syntax.Meta_pattern args ->
                                let args1 = norm_pattern_args cfg env args in
                                norm cfg env
                                  ((Meta
                                      ((FStar_Syntax_Syntax.Meta_pattern
                                          args1),
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) head1
                            | uu____14875 -> norm cfg env stack1 head1)
                       | [] ->
                           let head2 = norm cfg env [] head1 in
                           let m1 =
                             match m with
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let uu____14889 =
                                   norm_pattern_args cfg env args in
                                 FStar_Syntax_Syntax.Meta_pattern uu____14889
                             | uu____14900 -> m in
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
              let uu____14912 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____14912 with
              | (uu____14913,return_repr) ->
                  let return_inst =
                    let uu____14922 =
                      let uu____14923 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____14923.FStar_Syntax_Syntax.n in
                    match uu____14922 with
                    | FStar_Syntax_Syntax.Tm_uinst
                        (return_tm,uu____14929::[]) ->
                        let uu____14936 =
                          let uu____14939 =
                            let uu____14940 =
                              let uu____14947 =
                                let uu____14950 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____14950] in
                              (return_tm, uu____14947) in
                            FStar_Syntax_Syntax.Tm_uinst uu____14940 in
                          FStar_Syntax_Syntax.mk uu____14939 in
                        uu____14936 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____14958 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____14961 =
                    let uu____14964 =
                      let uu____14965 =
                        let uu____14980 =
                          let uu____14983 = FStar_Syntax_Syntax.as_arg t in
                          let uu____14984 =
                            let uu____14987 = FStar_Syntax_Syntax.as_arg e in
                            [uu____14987] in
                          uu____14983 :: uu____14984 in
                        (return_inst, uu____14980) in
                      FStar_Syntax_Syntax.Tm_app uu____14965 in
                    FStar_Syntax_Syntax.mk uu____14964 in
                  uu____14961 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____14996 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____14996 with
               | FStar_Pervasives_Native.None  ->
                   let uu____14999 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____14999
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____15000;
                     FStar_TypeChecker_Env.mtarget = uu____15001;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____15002;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____15013;
                     FStar_TypeChecker_Env.mtarget = uu____15014;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____15015;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____15033 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____15033)
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
                (fun uu____15089  ->
                   match uu____15089 with
                   | (a,imp) ->
                       let uu____15100 = norm cfg env [] a in
                       (uu____15100, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___225_15117 = comp1 in
            let uu____15120 =
              let uu____15121 =
                let uu____15130 = norm cfg env [] t in
                let uu____15131 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____15130, uu____15131) in
              FStar_Syntax_Syntax.Total uu____15121 in
            {
              FStar_Syntax_Syntax.n = uu____15120;
              FStar_Syntax_Syntax.pos =
                (uu___225_15117.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___225_15117.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___226_15146 = comp1 in
            let uu____15149 =
              let uu____15150 =
                let uu____15159 = norm cfg env [] t in
                let uu____15160 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____15159, uu____15160) in
              FStar_Syntax_Syntax.GTotal uu____15150 in
            {
              FStar_Syntax_Syntax.n = uu____15149;
              FStar_Syntax_Syntax.pos =
                (uu___226_15146.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___226_15146.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____15212  ->
                      match uu____15212 with
                      | (a,i) ->
                          let uu____15223 = norm cfg env [] a in
                          (uu____15223, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___179_15234  ->
                      match uu___179_15234 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____15238 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____15238
                      | f -> f)) in
            let uu___227_15242 = comp1 in
            let uu____15245 =
              let uu____15246 =
                let uu___228_15247 = ct in
                let uu____15248 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____15249 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____15252 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____15248;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___228_15247.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____15249;
                  FStar_Syntax_Syntax.effect_args = uu____15252;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____15246 in
            {
              FStar_Syntax_Syntax.n = uu____15245;
              FStar_Syntax_Syntax.pos =
                (uu___227_15242.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___227_15242.FStar_Syntax_Syntax.vars)
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
            (let uu___229_15270 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___229_15270.tcenv);
               delta_level = (uu___229_15270.delta_level);
               primitive_steps = (uu___229_15270.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____15275 = norm1 t in
          FStar_Syntax_Util.non_informative uu____15275 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____15278 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___230_15297 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.pos =
                (uu___230_15297.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___230_15297.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____15304 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____15304
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
                    let uu___231_15315 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___231_15315.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___231_15315.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___231_15315.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___232_15317 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___232_15317.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___232_15317.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___232_15317.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___232_15317.FStar_Syntax_Syntax.flags)
                    } in
              let uu___233_15318 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos =
                  (uu___233_15318.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___233_15318.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____15320 -> c
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____15323  ->
        match uu____15323 with
        | (x,imp) ->
            let uu____15326 =
              let uu___234_15327 = x in
              let uu____15328 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___234_15327.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___234_15327.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____15328
              } in
            (uu____15326, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____15334 =
          FStar_List.fold_left
            (fun uu____15352  ->
               fun b  ->
                 match uu____15352 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____15334 with | (nbs,uu____15380) -> FStar_List.rev nbs
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
            let uu____15396 =
              let uu___235_15397 = rc in
              let uu____15398 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___235_15397.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____15398;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___235_15397.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____15396
        | uu____15405 -> lopt
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
              ((let uu____15418 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____15418
                then
                  let time_now = FStar_Util.now () in
                  let uu____15420 =
                    let uu____15421 =
                      let uu____15422 =
                        FStar_Util.time_diff time_then time_now in
                      FStar_Pervasives_Native.snd uu____15422 in
                    FStar_Util.string_of_int uu____15421 in
                  let uu____15427 = FStar_Syntax_Print.term_to_string tm in
                  let uu____15428 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                    uu____15420 uu____15427 uu____15428
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___236_15446 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___236_15446.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____15539  ->
                    let uu____15540 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____15540);
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
              let uu____15576 =
                let uu___237_15577 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___237_15577.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___237_15577.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____15576
          | (Arg (Univ uu____15578,uu____15579,uu____15580))::uu____15581 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____15584,uu____15585))::uu____15586 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____15602),aq,r))::stack2 ->
              (log cfg
                 (fun uu____15631  ->
                    let uu____15632 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____15632);
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
                 (let uu____15642 = FStar_ST.op_Bang m in
                  match uu____15642 with
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
                  | FStar_Pervasives_Native.Some (uu____15762,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq)
                          FStar_Pervasives_Native.None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 =
                FStar_Syntax_Syntax.extend_app head1 (t, aq)
                  FStar_Pervasives_Native.None r in
              let uu____15786 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____15786
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____15796  ->
                    let uu____15797 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____15797);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____15802 =
                  log cfg
                    (fun uu____15807  ->
                       let uu____15808 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____15809 =
                         let uu____15810 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____15827  ->
                                   match uu____15827 with
                                   | (p,uu____15837,uu____15838) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____15810
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____15808 uu____15809);
                  (let whnf1 = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___180_15855  ->
                               match uu___180_15855 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____15856 -> false)) in
                     let steps' =
                       let uu____15860 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____15860
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     only_strong_steps
                       (let uu___238_15866 = cfg in
                        {
                          steps = (FStar_List.append steps' cfg.steps);
                          tcenv = (uu___238_15866.tcenv);
                          delta_level = new_delta;
                          primitive_steps = (uu___238_15866.primitive_steps)
                        }) in
                   let norm_or_whnf env2 t1 =
                     if whnf1
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____15910 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____15933 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____15999  ->
                                   fun uu____16000  ->
                                     match (uu____15999, uu____16000) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____16103 = norm_pat env3 p1 in
                                         (match uu____16103 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____15933 with
                          | (pats1,env3) ->
                              ((let uu___239_16205 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.p =
                                    (uu___239_16205.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___240_16224 = x in
                           let uu____16225 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___240_16224.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___240_16224.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16225
                           } in
                         ((let uu___241_16233 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.p =
                               (uu___241_16233.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___242_16238 = x in
                           let uu____16239 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___242_16238.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___242_16238.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16239
                           } in
                         ((let uu___243_16247 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.p =
                               (uu___243_16247.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___244_16257 = x in
                           let uu____16258 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___244_16257.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___244_16257.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16258
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___245_16267 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.p =
                               (uu___245_16267.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf1 -> branches
                     | uu____16271 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____16285 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____16285 with
                                 | (p,wopt,e) ->
                                     let uu____16305 = norm_pat env1 p in
                                     (match uu____16305 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Pervasives_Native.Some w
                                                ->
                                                let uu____16336 =
                                                  norm_or_whnf env2 w in
                                                FStar_Pervasives_Native.Some
                                                  uu____16336 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____16342 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____16342) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____16352) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____16357 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____16358;
                        FStar_Syntax_Syntax.fv_delta = uu____16359;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Data_ctor );_}
                      -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____16360;
                        FStar_Syntax_Syntax.fv_delta = uu____16361;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Record_ctor uu____16362);_}
                      -> true
                  | uu____16369 -> false in
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
                  let uu____16498 =
                    FStar_Syntax_Util.head_and_args scrutinee1 in
                  match uu____16498 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var uu____16547 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_wild uu____16550 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____16553 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee1.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____16572 ->
                                let uu____16573 =
                                  let uu____16574 = is_cons head1 in
                                  Prims.op_Negation uu____16574 in
                                FStar_Util.Inr uu____16573)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____16595 =
                             let uu____16596 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____16596.FStar_Syntax_Syntax.n in
                           (match uu____16595 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____16606 ->
                                let uu____16607 =
                                  let uu____16608 = is_cons head1 in
                                  Prims.op_Negation uu____16608 in
                                FStar_Util.Inr uu____16607))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____16661)::rest_a,(p1,uu____16664)::rest_p) ->
                      let uu____16708 = matches_pat t1 p1 in
                      (match uu____16708 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____16733 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____16835 = matches_pat scrutinee1 p1 in
                      (match uu____16835 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____16855  ->
                                 let uu____16856 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____16857 =
                                   let uu____16858 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____16858
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____16856 uu____16857);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____16875 =
                                        let uu____16876 =
                                          let uu____16895 =
                                            FStar_Util.mk_ref
                                              (FStar_Pervasives_Native.Some
                                                 ([], t1)) in
                                          ([], t1, uu____16895, false) in
                                        Clos uu____16876 in
                                      uu____16875 :: env2) env1 s in
                             let uu____16948 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____16948))) in
                let uu____16949 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____16949
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___181_16972  ->
                match uu___181_16972 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____16976 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____16982 -> d in
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
            let uu___246_17011 = config s e in
            {
              steps = (uu___246_17011.steps);
              tcenv = (uu___246_17011.tcenv);
              delta_level = (uu___246_17011.delta_level);
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
      fun t  -> let uu____17036 = config s e in norm_comp uu____17036 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____17045 = config [] env in norm_universe uu____17045 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let uu____17054 = config [] env in ghost_to_pure_aux uu____17054 [] c
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
        let uu____17068 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____17068 in
      let uu____17069 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____17069
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___247_17071 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___247_17071.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___247_17071.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____17074  ->
                    let uu____17075 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____17075))
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
            ((let uu____17094 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____17094);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____17107 = config [AllowUnboundUniverses] env in
          norm_comp uu____17107 [] c
        with
        | e ->
            ((let uu____17114 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____17114);
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
                   let uu____17154 =
                     let uu____17155 =
                       let uu____17162 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____17162) in
                     FStar_Syntax_Syntax.Tm_refine uu____17155 in
                   mk uu____17154 t01.FStar_Syntax_Syntax.pos
               | uu____17167 -> t2)
          | uu____17168 -> t2 in
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
        let uu____17220 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____17220 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____17249 ->
                 let uu____17256 = FStar_Syntax_Util.abs_formals e in
                 (match uu____17256 with
                  | (actuals,uu____17266,uu____17267) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____17281 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____17281 with
                         | (binders,args) ->
                             let uu____17298 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____17298
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
      | uu____17308 ->
          let uu____17309 = FStar_Syntax_Util.head_and_args t in
          (match uu____17309 with
           | (head1,args) ->
               let uu____17346 =
                 let uu____17347 = FStar_Syntax_Subst.compress head1 in
                 uu____17347.FStar_Syntax_Syntax.n in
               (match uu____17346 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____17350,thead) ->
                    let uu____17376 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____17376 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____17418 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___252_17426 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___252_17426.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___252_17426.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___252_17426.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___252_17426.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___252_17426.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___252_17426.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___252_17426.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___252_17426.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___252_17426.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___252_17426.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___252_17426.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___252_17426.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___252_17426.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___252_17426.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___252_17426.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___252_17426.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___252_17426.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___252_17426.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___252_17426.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___252_17426.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___252_17426.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___252_17426.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___252_17426.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___252_17426.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___252_17426.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___252_17426.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___252_17426.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___252_17426.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___252_17426.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___252_17426.FStar_TypeChecker_Env.dsenv)
                                 }) t in
                            match uu____17418 with
                            | (uu____17427,ty,uu____17429) ->
                                eta_expand_with_type env t ty))
                | uu____17430 ->
                    let uu____17431 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___253_17439 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___253_17439.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___253_17439.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___253_17439.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___253_17439.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___253_17439.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___253_17439.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___253_17439.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___253_17439.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___253_17439.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___253_17439.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___253_17439.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___253_17439.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___253_17439.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___253_17439.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___253_17439.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___253_17439.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___253_17439.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___253_17439.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___253_17439.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___253_17439.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___253_17439.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___253_17439.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___253_17439.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___253_17439.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___253_17439.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___253_17439.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___253_17439.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___253_17439.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___253_17439.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___253_17439.FStar_TypeChecker_Env.dsenv)
                         }) t in
                    (match uu____17431 with
                     | (uu____17440,ty,uu____17442) ->
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
            | (uu____17520,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____17526,FStar_Util.Inl t) ->
                let uu____17532 =
                  let uu____17535 =
                    let uu____17536 =
                      let uu____17549 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____17549) in
                    FStar_Syntax_Syntax.Tm_arrow uu____17536 in
                  FStar_Syntax_Syntax.mk uu____17535 in
                uu____17532 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____17553 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____17553 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____17580 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____17635 ->
                    let uu____17636 =
                      let uu____17645 =
                        let uu____17646 = FStar_Syntax_Subst.compress t3 in
                        uu____17646.FStar_Syntax_Syntax.n in
                      (uu____17645, tc) in
                    (match uu____17636 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____17671) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____17708) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____17747,FStar_Util.Inl uu____17748) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____17771 -> failwith "Impossible") in
              (match uu____17580 with
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
          let uu____17880 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____17880 with
          | (univ_names1,binders1,tc) ->
              let uu____17938 = FStar_Util.left tc in
              (univ_names1, binders1, uu____17938)
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
          let uu____17977 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____17977 with
          | (univ_names1,binders1,tc) ->
              let uu____18037 = FStar_Util.right tc in
              (univ_names1, binders1, uu____18037)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____18072 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____18072 with
           | (univ_names1,binders1,typ1) ->
               let uu___254_18100 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___254_18100.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___254_18100.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___254_18100.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___254_18100.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___255_18121 = s in
          let uu____18122 =
            let uu____18123 =
              let uu____18132 = FStar_List.map (elim_uvars env) sigs in
              (uu____18132, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____18123 in
          {
            FStar_Syntax_Syntax.sigel = uu____18122;
            FStar_Syntax_Syntax.sigrng =
              (uu___255_18121.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___255_18121.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___255_18121.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___255_18121.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____18149 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____18149 with
           | (univ_names1,uu____18167,typ1) ->
               let uu___256_18181 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___256_18181.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___256_18181.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___256_18181.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___256_18181.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____18187 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____18187 with
           | (univ_names1,uu____18205,typ1) ->
               let uu___257_18219 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___257_18219.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___257_18219.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___257_18219.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___257_18219.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____18253 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____18253 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____18276 =
                            let uu____18277 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____18277 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____18276 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___258_18280 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___258_18280.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___258_18280.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___259_18281 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___259_18281.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___259_18281.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___259_18281.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___259_18281.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___260_18293 = s in
          let uu____18294 =
            let uu____18295 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____18295 in
          {
            FStar_Syntax_Syntax.sigel = uu____18294;
            FStar_Syntax_Syntax.sigrng =
              (uu___260_18293.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___260_18293.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___260_18293.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___260_18293.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____18299 = elim_uvars_aux_t env us [] t in
          (match uu____18299 with
           | (us1,uu____18317,t1) ->
               let uu___261_18331 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___261_18331.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___261_18331.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___261_18331.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___261_18331.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____18332 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____18334 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____18334 with
           | (univs1,binders,signature) ->
               let uu____18362 =
                 let uu____18371 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____18371 with
                 | (univs_opening,univs2) ->
                     let uu____18398 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____18398) in
               (match uu____18362 with
                | (univs_opening,univs_closing) ->
                    let uu____18415 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____18421 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____18422 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____18421, uu____18422) in
                    (match uu____18415 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____18444 =
                           match uu____18444 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____18462 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____18462 with
                                | (us1,t1) ->
                                    let uu____18473 =
                                      let uu____18478 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____18485 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____18478, uu____18485) in
                                    (match uu____18473 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____18498 =
                                           let uu____18503 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____18512 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____18503, uu____18512) in
                                         (match uu____18498 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____18528 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____18528 in
                                              let uu____18529 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____18529 with
                                               | (uu____18550,uu____18551,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____18566 =
                                                       let uu____18567 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____18567 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____18566 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____18572 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____18572 with
                           | (uu____18585,uu____18586,t1) -> t1 in
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
                             | uu____18646 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____18663 =
                               let uu____18664 =
                                 FStar_Syntax_Subst.compress body in
                               uu____18664.FStar_Syntax_Syntax.n in
                             match uu____18663 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____18723 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____18752 =
                               let uu____18753 =
                                 FStar_Syntax_Subst.compress t in
                               uu____18753.FStar_Syntax_Syntax.n in
                             match uu____18752 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____18774) ->
                                 let uu____18795 = destruct_action_body body in
                                 (match uu____18795 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____18840 ->
                                 let uu____18841 = destruct_action_body t in
                                 (match uu____18841 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____18890 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____18890 with
                           | (action_univs,t) ->
                               let uu____18899 = destruct_action_typ_templ t in
                               (match uu____18899 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___262_18940 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___262_18940.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___262_18940.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___263_18942 = ed in
                           let uu____18943 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____18944 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____18945 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____18946 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____18947 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____18948 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____18949 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____18950 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____18951 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____18952 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____18953 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____18954 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____18955 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____18956 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___263_18942.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___263_18942.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____18943;
                             FStar_Syntax_Syntax.bind_wp = uu____18944;
                             FStar_Syntax_Syntax.if_then_else = uu____18945;
                             FStar_Syntax_Syntax.ite_wp = uu____18946;
                             FStar_Syntax_Syntax.stronger = uu____18947;
                             FStar_Syntax_Syntax.close_wp = uu____18948;
                             FStar_Syntax_Syntax.assert_p = uu____18949;
                             FStar_Syntax_Syntax.assume_p = uu____18950;
                             FStar_Syntax_Syntax.null_wp = uu____18951;
                             FStar_Syntax_Syntax.trivial = uu____18952;
                             FStar_Syntax_Syntax.repr = uu____18953;
                             FStar_Syntax_Syntax.return_repr = uu____18954;
                             FStar_Syntax_Syntax.bind_repr = uu____18955;
                             FStar_Syntax_Syntax.actions = uu____18956
                           } in
                         let uu___264_18959 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___264_18959.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___264_18959.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___264_18959.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___264_18959.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___182_18976 =
            match uu___182_18976 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____19003 = elim_uvars_aux_t env us [] t in
                (match uu____19003 with
                 | (us1,uu____19027,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___265_19046 = sub_eff in
            let uu____19047 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____19050 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___265_19046.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___265_19046.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____19047;
              FStar_Syntax_Syntax.lift = uu____19050
            } in
          let uu___266_19053 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___266_19053.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___266_19053.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___266_19053.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___266_19053.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____19063 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____19063 with
           | (univ_names1,binders1,comp1) ->
               let uu___267_19097 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___267_19097.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___267_19097.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___267_19097.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___267_19097.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____19108 -> s