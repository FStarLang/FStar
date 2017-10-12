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
    let uu____4314 = FStar_Syntax_Embeddings.unembed_list_safe u in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____4314 in
  let arg_as_bounded_int uu____4342 =
    match uu____4342 with
    | (a,uu____4354) ->
        let uu____4361 =
          let uu____4362 = FStar_Syntax_Subst.compress a in
          uu____4362.FStar_Syntax_Syntax.n in
        (match uu____4361 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____4372;
                FStar_Syntax_Syntax.vars = uu____4373;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____4375;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____4376;_},uu____4377)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____4416 =
               let uu____4421 = FStar_Util.int_of_string i in
               (fv1, uu____4421) in
             FStar_Pervasives_Native.Some uu____4416
         | uu____4426 -> FStar_Pervasives_Native.None) in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4468 = f a in FStar_Pervasives_Native.Some uu____4468
    | uu____4469 -> FStar_Pervasives_Native.None in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4519 = f a0 a1 in FStar_Pervasives_Native.Some uu____4519
    | uu____4520 -> FStar_Pervasives_Native.None in
  let unary_op as_a f r args =
    let uu____4569 = FStar_List.map as_a args in lift_unary (f r) uu____4569 in
  let binary_op as_a f r args =
    let uu____4625 = FStar_List.map as_a args in lift_binary (f r) uu____4625 in
  let as_primitive_step uu____4649 =
    match uu____4649 with
    | (l,arity,f) ->
        { name = l; arity; strong_reduction_ok = true; interpretation = f } in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  ->
         fun x  ->
           let uu____4697 = f x in
           FStar_Syntax_Embeddings.embed_int r uu____4697) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4725 = f x y in
             FStar_Syntax_Embeddings.embed_int r uu____4725) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____4746 = f x in
           FStar_Syntax_Embeddings.embed_bool r uu____4746) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4774 = f x y in
             FStar_Syntax_Embeddings.embed_bool r uu____4774) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4802 = f x y in
             FStar_Syntax_Embeddings.embed_string r uu____4802) in
  let list_of_string' rng s =
    let name l =
      let uu____4816 =
        let uu____4817 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____4817 in
      mk uu____4816 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____4827 =
      let uu____4830 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____4830 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____4827 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in
    FStar_Syntax_Embeddings.embed_int rng r in
  let string_concat' rng args =
    match args with
    | a1::a2::[] ->
        let uu____4877 = arg_as_string a1 in
        (match uu____4877 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4883 =
               arg_as_list FStar_Syntax_Embeddings.unembed_string_safe a2 in
             (match uu____4883 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____4896 = FStar_Syntax_Embeddings.embed_string rng r in
                  FStar_Pervasives_Native.Some uu____4896
              | uu____4897 -> FStar_Pervasives_Native.None)
         | uu____4902 -> FStar_Pervasives_Native.None)
    | uu____4905 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____4915 = FStar_Util.string_of_int i in
    FStar_Syntax_Embeddings.embed_string rng uu____4915 in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____4931 = FStar_Util.string_of_int i in
    FStar_Syntax_Embeddings.embed_string rng uu____4931 in
  let string_of_bool2 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false") in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r in
  let range_of1 uu____4961 args =
    match args with
    | uu____4973::(t,uu____4975)::[] ->
        let uu____5004 = term_of_range t.FStar_Syntax_Syntax.pos in
        FStar_Pervasives_Native.Some uu____5004
    | uu____5009 -> FStar_Pervasives_Native.None in
  let set_range_of1 r args =
    match args with
    | uu____5041::(t,uu____5043)::(r1,uu____5045)::[] ->
        let uu____5066 = FStar_Syntax_Embeddings.unembed_range_safe r1 in
        FStar_Util.bind_opt uu____5066
          (fun r2  ->
             FStar_Pervasives_Native.Some
               (let uu___202_5076 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___202_5076.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r2;
                  FStar_Syntax_Syntax.vars =
                    (uu___202_5076.FStar_Syntax_Syntax.vars)
                }))
    | uu____5077 -> FStar_Pervasives_Native.None in
  let mk_range1 r args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____5104 =
          let uu____5125 = arg_as_string fn in
          let uu____5128 = arg_as_int from_line in
          let uu____5131 = arg_as_int from_col in
          let uu____5134 = arg_as_int to_line in
          let uu____5137 = arg_as_int to_col in
          (uu____5125, uu____5128, uu____5131, uu____5134, uu____5137) in
        (match uu____5104 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r1 =
               let uu____5168 = FStar_Range.mk_pos from_l from_c in
               let uu____5169 = FStar_Range.mk_pos to_l to_c in
               FStar_Range.mk_range fn1 uu____5168 uu____5169 in
             let uu____5170 = term_of_range r1 in
             FStar_Pervasives_Native.Some uu____5170
         | uu____5175 -> FStar_Pervasives_Native.None)
    | uu____5196 -> FStar_Pervasives_Native.None in
  let decidable_eq neg rng args =
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) rng in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) rng in
    match args with
    | (_typ,uu____5222)::(a1,uu____5224)::(a2,uu____5226)::[] ->
        let uu____5263 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____5263 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____5276 -> FStar_Pervasives_Native.None)
    | uu____5277 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____5295 =
      let uu____5310 =
        let uu____5325 =
          let uu____5340 =
            let uu____5355 =
              let uu____5370 =
                let uu____5385 =
                  let uu____5400 =
                    let uu____5415 =
                      let uu____5430 =
                        let uu____5445 =
                          let uu____5460 =
                            let uu____5475 =
                              let uu____5490 =
                                let uu____5505 =
                                  let uu____5520 =
                                    let uu____5535 =
                                      let uu____5550 =
                                        let uu____5565 =
                                          let uu____5580 =
                                            let uu____5595 =
                                              let uu____5608 =
                                                FStar_Parser_Const.p2l
                                                  ["FStar";
                                                  "String";
                                                  "list_of_string"] in
                                              (uu____5608,
                                                (Prims.parse_int "1"),
                                                (unary_op arg_as_string
                                                   list_of_string')) in
                                            let uu____5615 =
                                              let uu____5630 =
                                                let uu____5643 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "string_of_list"] in
                                                (uu____5643,
                                                  (Prims.parse_int "1"),
                                                  (unary_op
                                                     (arg_as_list
                                                        FStar_Syntax_Embeddings.unembed_char_safe)
                                                     string_of_list')) in
                                              let uu____5652 =
                                                let uu____5667 =
                                                  let uu____5682 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "concat"] in
                                                  (uu____5682,
                                                    (Prims.parse_int "2"),
                                                    string_concat') in
                                                let uu____5691 =
                                                  let uu____5708 =
                                                    let uu____5729 =
                                                      FStar_Parser_Const.p2l
                                                        ["Prims"; "range_of"] in
                                                    (uu____5729,
                                                      (Prims.parse_int "2"),
                                                      range_of1) in
                                                  let uu____5744 =
                                                    let uu____5767 =
                                                      let uu____5786 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "set_range_of"] in
                                                      (uu____5786,
                                                        (Prims.parse_int "3"),
                                                        set_range_of1) in
                                                    let uu____5799 =
                                                      let uu____5820 =
                                                        let uu____5835 =
                                                          FStar_Parser_Const.p2l
                                                            ["Prims";
                                                            "mk_range"] in
                                                        (uu____5835,
                                                          (Prims.parse_int
                                                             "5"), mk_range1) in
                                                      [uu____5820] in
                                                    uu____5767 :: uu____5799 in
                                                  uu____5708 :: uu____5744 in
                                                uu____5667 :: uu____5691 in
                                              uu____5630 :: uu____5652 in
                                            uu____5595 :: uu____5615 in
                                          (FStar_Parser_Const.op_notEq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq true)) ::
                                            uu____5580 in
                                        (FStar_Parser_Const.op_Eq,
                                          (Prims.parse_int "3"),
                                          (decidable_eq false)) :: uu____5565 in
                                      (FStar_Parser_Const.string_compare,
                                        (Prims.parse_int "2"),
                                        (binary_op arg_as_string
                                           string_compare'))
                                        :: uu____5550 in
                                    (FStar_Parser_Const.string_of_bool_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_bool string_of_bool2))
                                      :: uu____5535 in
                                  (FStar_Parser_Const.string_of_int_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_int string_of_int2)) ::
                                    uu____5520 in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____5505 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5490 in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____5475 in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____5460 in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____5445 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____5430 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                FStar_Syntax_Embeddings.embed_bool r (x >= y))))
                      :: uu____5415 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              FStar_Syntax_Embeddings.embed_bool r (x > y))))
                    :: uu____5400 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            FStar_Syntax_Embeddings.embed_bool r (x <= y))))
                  :: uu____5385 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          FStar_Syntax_Embeddings.embed_bool r (x < y))))
                :: uu____5370 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____5355 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____5340 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____5325 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____5310 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____5295 in
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
      let uu____6424 =
        let uu____6425 =
          let uu____6426 = FStar_Syntax_Syntax.as_arg c in [uu____6426] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6425 in
      uu____6424 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____6461 =
              let uu____6474 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____6474, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____6493  ->
                        fun uu____6494  ->
                          match (uu____6493, uu____6494) with
                          | ((int_to_t1,x),(uu____6513,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____6523 =
              let uu____6538 =
                let uu____6551 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____6551, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____6570  ->
                          fun uu____6571  ->
                            match (uu____6570, uu____6571) with
                            | ((int_to_t1,x),(uu____6590,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____6600 =
                let uu____6615 =
                  let uu____6628 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____6628, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____6647  ->
                            fun uu____6648  ->
                              match (uu____6647, uu____6648) with
                              | ((int_to_t1,x),(uu____6667,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____6615] in
              uu____6538 :: uu____6600 in
            uu____6461 :: uu____6523)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop r args =
    match args with
    | (_typ,uu____6763)::(a1,uu____6765)::(a2,uu____6767)::[] ->
        let uu____6804 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6804 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___203_6810 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___203_6810.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___203_6810.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___204_6814 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___204_6814.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___204_6814.FStar_Syntax_Syntax.vars)
                })
         | uu____6815 -> FStar_Pervasives_Native.None)
    | (_typ,uu____6817)::uu____6818::(a1,uu____6820)::(a2,uu____6822)::[] ->
        let uu____6871 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6871 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___203_6877 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___203_6877.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___203_6877.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___204_6881 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___204_6881.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___204_6881.FStar_Syntax_Syntax.vars)
                })
         | uu____6882 -> FStar_Pervasives_Native.None)
    | uu____6883 -> failwith "Unexpected number of arguments" in
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
      let uu____6896 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops cfg.steps) in
      if uu____6896
      then tm
      else
        (let uu____6898 = FStar_Syntax_Util.head_and_args tm in
         match uu____6898 with
         | (head1,args) ->
             let uu____6935 =
               let uu____6936 = FStar_Syntax_Util.un_uinst head1 in
               uu____6936.FStar_Syntax_Syntax.n in
             (match uu____6935 with
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____6940 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps in
                  (match uu____6940 with
                   | FStar_Pervasives_Native.None  -> tm
                   | FStar_Pervasives_Native.Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then
                         (log cfg
                            (fun uu____6957  ->
                               let uu____6958 =
                                 FStar_Syntax_Print.lid_to_string
                                   prim_step.name in
                               let uu____6959 =
                                 FStar_Util.string_of_int
                                   (FStar_List.length args) in
                               let uu____6966 =
                                 FStar_Util.string_of_int prim_step.arity in
                               FStar_Util.print3
                                 "primop: found partially applied %s (%s/%s args)\n"
                                 uu____6958 uu____6959 uu____6966);
                          tm)
                       else
                         (log cfg
                            (fun uu____6971  ->
                               let uu____6972 =
                                 FStar_Syntax_Print.term_to_string tm in
                               FStar_Util.print1
                                 "primop: trying to reduce <%s>\n" uu____6972);
                          (let uu____6973 =
                             prim_step.interpretation
                               head1.FStar_Syntax_Syntax.pos args in
                           match uu____6973 with
                           | FStar_Pervasives_Native.None  ->
                               (log cfg
                                  (fun uu____6979  ->
                                     let uu____6980 =
                                       FStar_Syntax_Print.term_to_string tm in
                                     FStar_Util.print1
                                       "primop: <%s> did not reduce\n"
                                       uu____6980);
                                tm)
                           | FStar_Pervasives_Native.Some reduced ->
                               (log cfg
                                  (fun uu____6986  ->
                                     let uu____6987 =
                                       FStar_Syntax_Print.term_to_string tm in
                                     let uu____6988 =
                                       FStar_Syntax_Print.term_to_string
                                         reduced in
                                     FStar_Util.print2
                                       "primop: <%s> reduced to <%s>\n"
                                       uu____6987 uu____6988);
                                reduced))))
              | uu____6989 -> tm))
let reduce_equality:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___205_7000 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___205_7000.tcenv);
           delta_level = (uu___205_7000.delta_level);
           primitive_steps = equality_ops
         }) tm
let maybe_simplify:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      let tm1 = reduce_primops cfg tm in
      let uu____7010 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify cfg.steps) in
      if uu____7010
      then tm1
      else
        (let w t =
           let uu___206_7022 = t in
           {
             FStar_Syntax_Syntax.n = (uu___206_7022.FStar_Syntax_Syntax.n);
             FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
             FStar_Syntax_Syntax.vars =
               (uu___206_7022.FStar_Syntax_Syntax.vars)
           } in
         let simp_t t =
           match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
               -> FStar_Pervasives_Native.Some true
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
               -> FStar_Pervasives_Native.Some false
           | uu____7039 -> FStar_Pervasives_Native.None in
         let simplify1 arg =
           ((simp_t (FStar_Pervasives_Native.fst arg)), arg) in
         match tm1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.pos = uu____7079;
                     FStar_Syntax_Syntax.vars = uu____7080;_},uu____7081);
                FStar_Syntax_Syntax.pos = uu____7082;
                FStar_Syntax_Syntax.vars = uu____7083;_},args)
             ->
             let uu____7109 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
             if uu____7109
             then
               let uu____7110 =
                 FStar_All.pipe_right args (FStar_List.map simplify1) in
               (match uu____7110 with
                | (FStar_Pervasives_Native.Some (true ),uu____7165)::
                    (uu____7166,(arg,uu____7168))::[] -> arg
                | (uu____7233,(arg,uu____7235))::(FStar_Pervasives_Native.Some
                                                  (true ),uu____7236)::[]
                    -> arg
                | (FStar_Pervasives_Native.Some (false ),uu____7301)::uu____7302::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____7365::(FStar_Pervasives_Native.Some (false
                               ),uu____7366)::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____7429 -> tm1)
             else
               (let uu____7445 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
                if uu____7445
                then
                  let uu____7446 =
                    FStar_All.pipe_right args (FStar_List.map simplify1) in
                  match uu____7446 with
                  | (FStar_Pervasives_Native.Some (true ),uu____7501)::uu____7502::[]
                      -> w FStar_Syntax_Util.t_true
                  | uu____7565::(FStar_Pervasives_Native.Some (true
                                 ),uu____7566)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____7629)::
                      (uu____7630,(arg,uu____7632))::[] -> arg
                  | (uu____7697,(arg,uu____7699))::(FStar_Pervasives_Native.Some
                                                    (false ),uu____7700)::[]
                      -> arg
                  | uu____7765 -> tm1
                else
                  (let uu____7781 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.imp_lid in
                   if uu____7781
                   then
                     let uu____7782 =
                       FStar_All.pipe_right args (FStar_List.map simplify1) in
                     match uu____7782 with
                     | uu____7837::(FStar_Pervasives_Native.Some (true
                                    ),uu____7838)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____7901)::uu____7902::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____7965)::
                         (uu____7966,(arg,uu____7968))::[] -> arg
                     | (uu____8033,(p,uu____8035))::(uu____8036,(q,uu____8038))::[]
                         ->
                         let uu____8103 = FStar_Syntax_Util.term_eq p q in
                         (if uu____8103
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____8105 -> tm1
                   else
                     (let uu____8121 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____8121
                      then
                        let uu____8122 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1) in
                        match uu____8122 with
                        | (FStar_Pervasives_Native.Some (true ),uu____8177)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____8216)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____8255 -> tm1
                      else
                        (let uu____8271 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____8271
                         then
                           match args with
                           | (t,uu____8273)::[] ->
                               let uu____8290 =
                                 let uu____8291 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____8291.FStar_Syntax_Syntax.n in
                               (match uu____8290 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____8294::[],body,uu____8296) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____8323 -> tm1)
                                | uu____8326 -> tm1)
                           | (uu____8327,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____8328))::
                               (t,uu____8330)::[] ->
                               let uu____8369 =
                                 let uu____8370 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____8370.FStar_Syntax_Syntax.n in
                               (match uu____8369 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____8373::[],body,uu____8375) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____8402 -> tm1)
                                | uu____8405 -> tm1)
                           | uu____8406 -> tm1
                         else
                           (let uu____8416 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____8416
                            then
                              match args with
                              | (t,uu____8418)::[] ->
                                  let uu____8435 =
                                    let uu____8436 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____8436.FStar_Syntax_Syntax.n in
                                  (match uu____8435 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____8439::[],body,uu____8441) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____8468 -> tm1)
                                   | uu____8471 -> tm1)
                              | (uu____8472,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____8473))::
                                  (t,uu____8475)::[] ->
                                  let uu____8514 =
                                    let uu____8515 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____8515.FStar_Syntax_Syntax.n in
                                  (match uu____8514 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____8518::[],body,uu____8520) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____8547 -> tm1)
                                   | uu____8550 -> tm1)
                              | uu____8551 -> tm1
                            else reduce_equality cfg tm1)))))
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                FStar_Syntax_Syntax.pos = uu____8562;
                FStar_Syntax_Syntax.vars = uu____8563;_},args)
             ->
             let uu____8585 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
             if uu____8585
             then
               let uu____8586 =
                 FStar_All.pipe_right args (FStar_List.map simplify1) in
               (match uu____8586 with
                | (FStar_Pervasives_Native.Some (true ),uu____8641)::
                    (uu____8642,(arg,uu____8644))::[] -> arg
                | (uu____8709,(arg,uu____8711))::(FStar_Pervasives_Native.Some
                                                  (true ),uu____8712)::[]
                    -> arg
                | (FStar_Pervasives_Native.Some (false ),uu____8777)::uu____8778::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____8841::(FStar_Pervasives_Native.Some (false
                               ),uu____8842)::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____8905 -> tm1)
             else
               (let uu____8921 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
                if uu____8921
                then
                  let uu____8922 =
                    FStar_All.pipe_right args (FStar_List.map simplify1) in
                  match uu____8922 with
                  | (FStar_Pervasives_Native.Some (true ),uu____8977)::uu____8978::[]
                      -> w FStar_Syntax_Util.t_true
                  | uu____9041::(FStar_Pervasives_Native.Some (true
                                 ),uu____9042)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____9105)::
                      (uu____9106,(arg,uu____9108))::[] -> arg
                  | (uu____9173,(arg,uu____9175))::(FStar_Pervasives_Native.Some
                                                    (false ),uu____9176)::[]
                      -> arg
                  | uu____9241 -> tm1
                else
                  (let uu____9257 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.imp_lid in
                   if uu____9257
                   then
                     let uu____9258 =
                       FStar_All.pipe_right args (FStar_List.map simplify1) in
                     match uu____9258 with
                     | uu____9313::(FStar_Pervasives_Native.Some (true
                                    ),uu____9314)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____9377)::uu____9378::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____9441)::
                         (uu____9442,(arg,uu____9444))::[] -> arg
                     | (uu____9509,(p,uu____9511))::(uu____9512,(q,uu____9514))::[]
                         ->
                         let uu____9579 = FStar_Syntax_Util.term_eq p q in
                         (if uu____9579
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____9581 -> tm1
                   else
                     (let uu____9597 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____9597
                      then
                        let uu____9598 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1) in
                        match uu____9598 with
                        | (FStar_Pervasives_Native.Some (true ),uu____9653)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____9692)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____9731 -> tm1
                      else
                        (let uu____9747 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____9747
                         then
                           match args with
                           | (t,uu____9749)::[] ->
                               let uu____9766 =
                                 let uu____9767 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____9767.FStar_Syntax_Syntax.n in
                               (match uu____9766 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____9770::[],body,uu____9772) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____9799 -> tm1)
                                | uu____9802 -> tm1)
                           | (uu____9803,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____9804))::
                               (t,uu____9806)::[] ->
                               let uu____9845 =
                                 let uu____9846 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____9846.FStar_Syntax_Syntax.n in
                               (match uu____9845 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____9849::[],body,uu____9851) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____9878 -> tm1)
                                | uu____9881 -> tm1)
                           | uu____9882 -> tm1
                         else
                           (let uu____9892 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____9892
                            then
                              match args with
                              | (t,uu____9894)::[] ->
                                  let uu____9911 =
                                    let uu____9912 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____9912.FStar_Syntax_Syntax.n in
                                  (match uu____9911 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____9915::[],body,uu____9917) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____9944 -> tm1)
                                   | uu____9947 -> tm1)
                              | (uu____9948,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____9949))::
                                  (t,uu____9951)::[] ->
                                  let uu____9990 =
                                    let uu____9991 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____9991.FStar_Syntax_Syntax.n in
                                  (match uu____9990 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____9994::[],body,uu____9996) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____10023 -> tm1)
                                   | uu____10026 -> tm1)
                              | uu____10027 -> tm1
                            else reduce_equality cfg tm1)))))
         | uu____10037 -> tm1)
let is_norm_request:
  'Auu____10044 .
    FStar_Syntax_Syntax.term -> 'Auu____10044 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10057 =
        let uu____10064 =
          let uu____10065 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10065.FStar_Syntax_Syntax.n in
        (uu____10064, args) in
      match uu____10057 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10071::uu____10072::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10076::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10081::uu____10082::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10085 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___173_10097  ->
    match uu___173_10097 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.WHNF  -> [WHNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10103 =
          let uu____10106 =
            let uu____10107 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____10107 in
          [uu____10106] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10103
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____10126 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10126) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10164 =
          let uu____10167 =
            let uu____10172 =
              FStar_Syntax_Embeddings.unembed_list
                FStar_Syntax_Embeddings.unembed_norm_step in
            uu____10172 s in
          FStar_All.pipe_right uu____10167 FStar_Util.must in
        FStar_All.pipe_right uu____10164 tr_norm_steps in
      match args with
      | uu____10197::(tm,uu____10199)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____10222)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____10237)::uu____10238::(tm,uu____10240)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____10280 =
              let uu____10283 = full_norm steps in parse_steps uu____10283 in
            Beta :: uu____10280 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____10292 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___174_10310  ->
    match uu___174_10310 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.pos = uu____10313;
           FStar_Syntax_Syntax.vars = uu____10314;_},uu____10315,uu____10316))::uu____10317
        -> true
    | uu____10324 -> false
let should_reify: cfg -> stack_elt Prims.list -> Prims.bool =
  fun cfg  ->
    fun stack1  ->
      match stack1 with
      | (App
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify );
             FStar_Syntax_Syntax.pos = uu____10339;
             FStar_Syntax_Syntax.vars = uu____10340;_},uu____10341,uu____10342))::uu____10343
          -> FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)
      | uu____10350 -> false
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
            (fun uu____10497  ->
               let uu____10498 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____10499 = FStar_Syntax_Print.term_to_string t1 in
               let uu____10500 =
                 let uu____10501 =
                   let uu____10504 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____10504 in
                 stack_to_string uu____10501 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____10498
                 uu____10499 uu____10500);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____10527 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____10552 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____10569 =
                 let uu____10570 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____10571 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____10570 uu____10571 in
               failwith uu____10569
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____10572 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____10589 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____10590 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10591;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____10592;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10595;
                 FStar_Syntax_Syntax.fv_delta = uu____10596;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10597;
                 FStar_Syntax_Syntax.fv_delta = uu____10598;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____10599);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar fv when
               let uu____10607 = FStar_Syntax_Syntax.lid_of_fv fv in
               FStar_TypeChecker_Env.is_action cfg.tcenv uu____10607 ->
               let b = should_reify cfg stack1 in
               (log cfg
                  (fun uu____10613  ->
                     let uu____10614 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____10615 = FStar_Util.string_of_bool b in
                     FStar_Util.print2
                       ">>> For DM4F action %s, should_reify = %s\n"
                       uu____10614 uu____10615);
                if b
                then
                  (let uu____10616 = FStar_List.tl stack1 in
                   do_unfold_fv cfg env uu____10616 t1 fv)
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
                 let uu___207_10655 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___207_10655.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___207_10655.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____10688 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____10688) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___208_10696 = cfg in
                 let uu____10697 =
                   FStar_List.filter
                     (fun uu___175_10700  ->
                        match uu___175_10700 with
                        | UnfoldOnly uu____10701 -> false
                        | NoDeltaSteps  -> false
                        | uu____10704 -> true) cfg.steps in
                 {
                   steps = uu____10697;
                   tcenv = (uu___208_10696.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___208_10696.primitive_steps)
                 } in
               let uu____10705 = get_norm_request (norm cfg' env []) args in
               (match uu____10705 with
                | (s,tm) ->
                    let delta_level =
                      let uu____10721 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___176_10726  ->
                                match uu___176_10726 with
                                | UnfoldUntil uu____10727 -> true
                                | UnfoldOnly uu____10728 -> true
                                | uu____10731 -> false)) in
                      if uu____10721
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___209_10736 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___209_10736.tcenv);
                        delta_level;
                        primitive_steps = (uu___209_10736.primitive_steps)
                      } in
                    let stack' =
                      let tail1 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let uu____10747 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____10747
                      then
                        let uu____10750 =
                          let uu____10751 =
                            let uu____10756 = FStar_Util.now () in
                            (t1, uu____10756) in
                          Debug uu____10751 in
                        uu____10750 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____10758;
                  FStar_Syntax_Syntax.vars = uu____10759;_},a1::a2::rest)
               ->
               let uu____10807 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____10807 with
                | (hd1,uu____10823) ->
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
                    (FStar_Const.Const_reflect uu____10888);
                  FStar_Syntax_Syntax.pos = uu____10889;
                  FStar_Syntax_Syntax.vars = uu____10890;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____10922 = FStar_List.tl stack1 in
               norm cfg env uu____10922 (FStar_Pervasives_Native.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____10925;
                  FStar_Syntax_Syntax.vars = uu____10926;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____10958 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____10958 with
                | (reify_head,uu____10974) ->
                    let a1 =
                      let uu____10996 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (FStar_Pervasives_Native.fst a) in
                      FStar_Syntax_Subst.compress uu____10996 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____10999);
                            FStar_Syntax_Syntax.pos = uu____11000;
                            FStar_Syntax_Syntax.vars = uu____11001;_},a2::[])
                         ->
                         norm cfg env stack1 (FStar_Pervasives_Native.fst a2)
                     | uu____11035 ->
                         let stack2 =
                           (App
                              (reify_head, FStar_Pervasives_Native.None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11045 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____11045
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11052 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11052
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____11055 =
                      let uu____11062 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11062, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11055 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___177_11075  ->
                         match uu___177_11075 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11078 =
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
                 if uu____11078
                 then false
                 else
                   (let uu____11080 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___178_11087  ->
                              match uu___178_11087 with
                              | UnfoldOnly uu____11088 -> true
                              | uu____11091 -> false)) in
                    match uu____11080 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11095 -> should_delta) in
               (log cfg
                  (fun uu____11103  ->
                     let uu____11104 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11105 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____11106 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11104 uu____11105 uu____11106);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack1 t1
                else do_unfold_fv cfg env stack1 t1 f)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11109 = lookup_bvar env x in
               (match uu____11109 with
                | Univ uu____11110 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11135 = FStar_ST.op_Bang r in
                      (match uu____11135 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11236  ->
                                 let uu____11237 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____11238 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11237
                                   uu____11238);
                            (let uu____11239 =
                               let uu____11240 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____11240.FStar_Syntax_Syntax.n in
                             match uu____11239 with
                             | FStar_Syntax_Syntax.Tm_abs uu____11243 ->
                                 norm cfg env2 stack1 t'
                             | uu____11260 -> rebuild cfg env2 stack1 t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____11312)::uu____11313 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11322)::uu____11323 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11333,uu____11334))::stack_rest ->
                    (match c with
                     | Univ uu____11338 -> norm cfg (c :: env) stack_rest t1
                     | uu____11339 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____11344::[] ->
                              (log cfg
                                 (fun uu____11360  ->
                                    let uu____11361 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11361);
                               norm cfg (c :: env) stack_rest body)
                          | uu____11362::tl1 ->
                              (log cfg
                                 (fun uu____11381  ->
                                    let uu____11382 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11382);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___210_11412 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___210_11412.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____11497  ->
                          let uu____11498 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11498);
                     norm cfg env stack2 t1)
                | (Debug uu____11499)::uu____11500 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11507 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11507
                    else
                      (let uu____11509 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11509 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11533  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11549 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11549
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11559 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11559)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___211_11564 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___211_11564.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___211_11564.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11565 -> lopt in
                           (log cfg
                              (fun uu____11571  ->
                                 let uu____11572 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11572);
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
                | (Meta uu____11589)::uu____11590 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11597 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11597
                    else
                      (let uu____11599 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11599 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11623  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11639 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11639
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11649 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11649)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___211_11654 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___211_11654.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___211_11654.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11655 -> lopt in
                           (log cfg
                              (fun uu____11661  ->
                                 let uu____11662 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11662);
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
                | (Let uu____11679)::uu____11680 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11691 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11691
                    else
                      (let uu____11693 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11693 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11717  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11733 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11733
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11743 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11743)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___211_11748 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___211_11748.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___211_11748.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11749 -> lopt in
                           (log cfg
                              (fun uu____11755  ->
                                 let uu____11756 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11756);
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
                | (App uu____11773)::uu____11774 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11783 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11783
                    else
                      (let uu____11785 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11785 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11809  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11825 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11825
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11835 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11835)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___211_11840 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___211_11840.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___211_11840.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11841 -> lopt in
                           (log cfg
                              (fun uu____11847  ->
                                 let uu____11848 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11848);
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
                | (Abs uu____11865)::uu____11866 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11881 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11881
                    else
                      (let uu____11883 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11883 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11907  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11923 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11923
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11933 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11933)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___211_11938 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___211_11938.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___211_11938.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11939 -> lopt in
                           (log cfg
                              (fun uu____11945  ->
                                 let uu____11946 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11946);
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
                      let uu____11963 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11963
                    else
                      (let uu____11965 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11965 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11989  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12005 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12005
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12015 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12015)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___211_12020 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___211_12020.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___211_12020.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12021 -> lopt in
                           (log cfg
                              (fun uu____12027  ->
                                 let uu____12028 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12028);
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
                      (fun uu____12083  ->
                         fun stack2  ->
                           match uu____12083 with
                           | (a,aq) ->
                               let uu____12095 =
                                 let uu____12096 =
                                   let uu____12103 =
                                     let uu____12104 =
                                       let uu____12123 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____12123, false) in
                                     Clos uu____12104 in
                                   (uu____12103, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____12096 in
                               uu____12095 :: stack2) args) in
               (log cfg
                  (fun uu____12175  ->
                     let uu____12176 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12176);
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
                             ((let uu___212_12200 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___212_12200.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___212_12200.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____12201 ->
                      let uu____12206 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12206)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____12209 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____12209 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____12234 =
                          let uu____12235 =
                            let uu____12242 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___213_12244 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___213_12244.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___213_12244.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12242) in
                          FStar_Syntax_Syntax.Tm_refine uu____12235 in
                        mk uu____12234 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____12263 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____12263
               else
                 (let uu____12265 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____12265 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12273 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12285  -> Dummy :: env1) env) in
                        norm_comp cfg uu____12273 c1 in
                      let t2 =
                        let uu____12295 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____12295 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____12354)::uu____12355 ->
                    (log cfg
                       (fun uu____12366  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | (Arg uu____12367)::uu____12368 ->
                    (log cfg
                       (fun uu____12379  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | (App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____12380;
                       FStar_Syntax_Syntax.vars = uu____12381;_},uu____12382,uu____12383))::uu____12384
                    ->
                    (log cfg
                       (fun uu____12393  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | (MemoLazy uu____12394)::uu____12395 ->
                    (log cfg
                       (fun uu____12406  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | uu____12407 ->
                    (log cfg
                       (fun uu____12410  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11 in
                      log cfg
                        (fun uu____12414  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____12431 = norm cfg env [] t2 in
                             FStar_Util.Inl uu____12431
                         | FStar_Util.Inr c ->
                             let uu____12439 = norm_comp cfg env c in
                             FStar_Util.Inr uu____12439 in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env []) in
                       let uu____12445 =
                         let uu____12446 =
                           let uu____12447 =
                             let uu____12474 =
                               FStar_Syntax_Util.unascribe t12 in
                             (uu____12474, (tc1, tacopt1), l) in
                           FStar_Syntax_Syntax.Tm_ascribed uu____12447 in
                         mk uu____12446 t1.FStar_Syntax_Syntax.pos in
                       rebuild cfg env stack1 uu____12445))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____12550,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____12551;
                               FStar_Syntax_Syntax.lbunivs = uu____12552;
                               FStar_Syntax_Syntax.lbtyp = uu____12553;
                               FStar_Syntax_Syntax.lbeff = uu____12554;
                               FStar_Syntax_Syntax.lbdef = uu____12555;_}::uu____12556),uu____12557)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____12593 =
                 (let uu____12596 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____12596) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____12598 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____12598))) in
               if uu____12593
               then
                 let env1 =
                   let uu____12602 =
                     let uu____12603 =
                       let uu____12622 =
                         FStar_Util.mk_ref FStar_Pervasives_Native.None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____12622,
                         false) in
                     Clos uu____12603 in
                   uu____12602 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____12674 =
                    let uu____12679 =
                      let uu____12680 =
                        let uu____12681 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____12681
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____12680] in
                    FStar_Syntax_Subst.open_term uu____12679 body in
                  match uu____12674 with
                  | (bs,body1) ->
                      let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                      let lbname =
                        let x =
                          let uu____12695 = FStar_List.hd bs in
                          FStar_Pervasives_Native.fst uu____12695 in
                        FStar_Util.Inl
                          (let uu___214_12705 = x in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___214_12705.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___214_12705.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = ty
                           }) in
                      let lb1 =
                        let uu___215_12707 = lb in
                        let uu____12708 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = lbname;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___215_12707.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = ty;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___215_12707.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____12708
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____12725  -> Dummy :: env1)
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
               let uu____12749 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____12749 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____12785 =
                               let uu___216_12786 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___216_12786.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___216_12786.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____12785 in
                           let uu____12787 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____12787 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____12807 =
                                   FStar_List.map (fun uu____12811  -> Dummy)
                                     lbs1 in
                                 let uu____12812 =
                                   let uu____12815 =
                                     FStar_List.map
                                       (fun uu____12823  -> Dummy) xs1 in
                                   FStar_List.append uu____12815 env in
                                 FStar_List.append uu____12807 uu____12812 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____12835 =
                                       let uu___217_12836 = rc in
                                       let uu____12837 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___217_12836.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____12837;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___217_12836.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____12835
                                 | uu____12844 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___218_12848 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___218_12848.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___218_12848.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____12852 =
                        FStar_List.map (fun uu____12856  -> Dummy) lbs2 in
                      FStar_List.append uu____12852 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____12858 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____12858 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___219_12874 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___219_12874.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___219_12874.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____12901 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____12901
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____12920 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____12971  ->
                        match uu____12971 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____13044 =
                                let uu___220_13045 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___220_13045.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___220_13045.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____13044 in
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
               (match uu____12920 with
                | (rec_env,memos,uu____13173) ->
                    let uu____13202 =
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
                             let uu____13667 =
                               let uu____13668 =
                                 let uu____13687 =
                                   FStar_Util.mk_ref
                                     FStar_Pervasives_Native.None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____13687, false) in
                               Clos uu____13668 in
                             uu____13667 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
                    norm cfg body_env stack1 body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (match m with
                | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                    let uu____13754 =
                      let uu____13755 = should_reify cfg stack1 in
                      Prims.op_Negation uu____13755 in
                    if uu____13754
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____13765 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____13765
                        then
                          let uu___221_13766 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___221_13766.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps =
                              (uu___221_13766.primitive_steps)
                          }
                        else
                          (let uu___222_13768 = cfg in
                           {
                             steps =
                               (FStar_List.append [Exclude Zeta] cfg.steps);
                             tcenv = (uu___222_13768.tcenv);
                             delta_level = (uu___222_13768.delta_level);
                             primitive_steps =
                               (uu___222_13768.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____13770 =
                         let uu____13771 = FStar_Syntax_Subst.compress head1 in
                         uu____13771.FStar_Syntax_Syntax.n in
                       match uu____13770 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____13789 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____13789 with
                            | (uu____13790,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____13796 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____13804 =
                                         let uu____13805 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____13805.FStar_Syntax_Syntax.n in
                                       match uu____13804 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____13811,uu____13812))
                                           ->
                                           let uu____13821 =
                                             let uu____13822 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____13822.FStar_Syntax_Syntax.n in
                                           (match uu____13821 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____13828,msrc,uu____13830))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____13839 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____13839
                                            | uu____13840 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____13841 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____13842 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____13842 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___223_13847 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___223_13847.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___223_13847.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___223_13847.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____13848 =
                                            FStar_List.tl stack1 in
                                          let uu____13849 =
                                            let uu____13850 =
                                              let uu____13853 =
                                                let uu____13854 =
                                                  let uu____13867 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____13867) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____13854 in
                                              FStar_Syntax_Syntax.mk
                                                uu____13853 in
                                            uu____13850
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____13848
                                            uu____13849
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____13883 =
                                            let uu____13884 = is_return body in
                                            match uu____13884 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____13888;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____13889;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____13894 -> false in
                                          if uu____13883
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
                                               let uu____13918 =
                                                 let uu____13921 =
                                                   let uu____13922 =
                                                     let uu____13939 =
                                                       let uu____13942 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____13942] in
                                                     (uu____13939, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc)) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____13922 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____13921 in
                                               uu____13918
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____13958 =
                                                 let uu____13959 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____13959.FStar_Syntax_Syntax.n in
                                               match uu____13958 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____13965::uu____13966::[])
                                                   ->
                                                   let uu____13973 =
                                                     let uu____13976 =
                                                       let uu____13977 =
                                                         let uu____13984 =
                                                           let uu____13987 =
                                                             let uu____13988
                                                               =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____13988 in
                                                           let uu____13989 =
                                                             let uu____13992
                                                               =
                                                               let uu____13993
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____13993 in
                                                             [uu____13992] in
                                                           uu____13987 ::
                                                             uu____13989 in
                                                         (bind1, uu____13984) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____13977 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____13976 in
                                                   uu____13973
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____14001 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____14007 =
                                                 let uu____14010 =
                                                   let uu____14011 =
                                                     let uu____14026 =
                                                       let uu____14029 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____14030 =
                                                         let uu____14033 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____14034 =
                                                           let uu____14037 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____14038 =
                                                             let uu____14041
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____14042
                                                               =
                                                               let uu____14045
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____14046
                                                                 =
                                                                 let uu____14049
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____14049] in
                                                               uu____14045 ::
                                                                 uu____14046 in
                                                             uu____14041 ::
                                                               uu____14042 in
                                                           uu____14037 ::
                                                             uu____14038 in
                                                         uu____14033 ::
                                                           uu____14034 in
                                                       uu____14029 ::
                                                         uu____14030 in
                                                     (bind_inst, uu____14026) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____14011 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____14010 in
                                               uu____14007
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____14057 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____14057 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____14081 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____14081 with
                            | (uu____14082,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____14117 =
                                        let uu____14118 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____14118.FStar_Syntax_Syntax.n in
                                      match uu____14117 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____14124) -> t4
                                      | uu____14129 -> head2 in
                                    let uu____14130 =
                                      let uu____14131 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____14131.FStar_Syntax_Syntax.n in
                                    match uu____14130 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____14137 ->
                                        FStar_Pervasives_Native.None in
                                  let uu____14138 = maybe_extract_fv head2 in
                                  match uu____14138 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____14148 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____14148
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____14153 =
                                          maybe_extract_fv head3 in
                                        match uu____14153 with
                                        | FStar_Pervasives_Native.Some
                                            uu____14158 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____14159 ->
                                            FStar_Pervasives_Native.Some
                                              false in
                                      (head3, action_unfolded)
                                  | uu____14164 ->
                                      (head2, FStar_Pervasives_Native.None) in
                                ((let is_arg_impure uu____14179 =
                                    match uu____14179 with
                                    | (e,q) ->
                                        let uu____14186 =
                                          let uu____14187 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____14187.FStar_Syntax_Syntax.n in
                                        (match uu____14186 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____14202 -> false) in
                                  let uu____14203 =
                                    let uu____14204 =
                                      let uu____14211 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____14211 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____14204 in
                                  if uu____14203
                                  then
                                    let uu____14216 =
                                      let uu____14217 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____14217 in
                                    failwith uu____14216
                                  else ());
                                 (let uu____14219 =
                                    maybe_unfold_action head_app in
                                  match uu____14219 with
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
                                      let uu____14258 = FStar_List.tl stack1 in
                                      norm cfg env uu____14258 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____14272 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____14272 in
                           let uu____14273 = FStar_List.tl stack1 in
                           norm cfg env uu____14273 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____14394  ->
                                     match uu____14394 with
                                     | (pat,wopt,tm) ->
                                         let uu____14442 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____14442))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____14474 = FStar_List.tl stack1 in
                           norm cfg env uu____14474 tm
                       | uu____14475 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let uu____14483 = should_reify cfg stack1 in
                    if uu____14483
                    then
                      let uu____14484 = FStar_List.tl stack1 in
                      let uu____14485 =
                        let uu____14486 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____14486 in
                      norm cfg env uu____14484 uu____14485
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____14489 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____14489
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___224_14498 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___224_14498.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___224_14498.primitive_steps)
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
                | uu____14500 ->
                    if FStar_List.contains Unmeta cfg.steps
                    then norm cfg env stack1 head1
                    else
                      (match stack1 with
                       | uu____14502::uu____14503 ->
                           (match m with
                            | FStar_Syntax_Syntax.Meta_labeled
                                (l,r,uu____14508) ->
                                norm cfg env ((Meta (m, r)) :: stack1) head1
                            | FStar_Syntax_Syntax.Meta_alien uu____14509 ->
                                rebuild cfg env stack1 t1
                            | FStar_Syntax_Syntax.Meta_pattern args ->
                                let args1 = norm_pattern_args cfg env args in
                                norm cfg env
                                  ((Meta
                                      ((FStar_Syntax_Syntax.Meta_pattern
                                          args1),
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) head1
                            | uu____14540 -> norm cfg env stack1 head1)
                       | [] ->
                           let head2 = norm cfg env [] head1 in
                           let m1 =
                             match m with
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let uu____14554 =
                                   norm_pattern_args cfg env args in
                                 FStar_Syntax_Syntax.Meta_pattern uu____14554
                             | uu____14565 -> m in
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
              let uu____14577 = FStar_Syntax_Syntax.range_of_fv f in
              FStar_TypeChecker_Env.set_range cfg.tcenv uu____14577 in
            let uu____14578 =
              FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            match uu____14578 with
            | FStar_Pervasives_Native.None  ->
                (log cfg
                   (fun uu____14591  ->
                      FStar_Util.print "Tm_fvar case 2\n" []);
                 rebuild cfg env stack1 t0)
            | FStar_Pervasives_Native.Some (us,t) ->
                (log cfg
                   (fun uu____14602  ->
                      let uu____14603 = FStar_Syntax_Print.term_to_string t0 in
                      let uu____14604 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____14603
                        uu____14604);
                 (let t1 =
                    let uu____14606 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.contains
                           (UnfoldUntil FStar_Syntax_Syntax.Delta_constant)) in
                    if uu____14606
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
                    | (UnivArgs (us',uu____14616))::stack2 ->
                        let env1 =
                          FStar_All.pipe_right us'
                            (FStar_List.fold_left
                               (fun env1  -> fun u  -> (Univ u) :: env1) env) in
                        norm cfg env1 stack2 t1
                    | uu____14639 when
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains EraseUniverses)
                        -> norm cfg env stack1 t1
                    | uu____14642 ->
                        let uu____14645 =
                          let uu____14646 =
                            FStar_Syntax_Print.lid_to_string
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                          FStar_Util.format1
                            "Impossible: missing universe instantiation on %s"
                            uu____14646 in
                        failwith uu____14645
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
              let uu____14656 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____14656 with
              | (uu____14657,return_repr) ->
                  let return_inst =
                    let uu____14666 =
                      let uu____14667 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____14667.FStar_Syntax_Syntax.n in
                    match uu____14666 with
                    | FStar_Syntax_Syntax.Tm_uinst
                        (return_tm,uu____14673::[]) ->
                        let uu____14680 =
                          let uu____14683 =
                            let uu____14684 =
                              let uu____14691 =
                                let uu____14694 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____14694] in
                              (return_tm, uu____14691) in
                            FStar_Syntax_Syntax.Tm_uinst uu____14684 in
                          FStar_Syntax_Syntax.mk uu____14683 in
                        uu____14680 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____14702 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____14705 =
                    let uu____14708 =
                      let uu____14709 =
                        let uu____14724 =
                          let uu____14727 = FStar_Syntax_Syntax.as_arg t in
                          let uu____14728 =
                            let uu____14731 = FStar_Syntax_Syntax.as_arg e in
                            [uu____14731] in
                          uu____14727 :: uu____14728 in
                        (return_inst, uu____14724) in
                      FStar_Syntax_Syntax.Tm_app uu____14709 in
                    FStar_Syntax_Syntax.mk uu____14708 in
                  uu____14705 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____14740 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____14740 with
               | FStar_Pervasives_Native.None  ->
                   let uu____14743 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____14743
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____14744;
                     FStar_TypeChecker_Env.mtarget = uu____14745;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____14746;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____14757;
                     FStar_TypeChecker_Env.mtarget = uu____14758;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____14759;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____14777 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____14777)
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
                (fun uu____14833  ->
                   match uu____14833 with
                   | (a,imp) ->
                       let uu____14844 = norm cfg env [] a in
                       (uu____14844, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___225_14861 = comp1 in
            let uu____14864 =
              let uu____14865 =
                let uu____14874 = norm cfg env [] t in
                let uu____14875 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____14874, uu____14875) in
              FStar_Syntax_Syntax.Total uu____14865 in
            {
              FStar_Syntax_Syntax.n = uu____14864;
              FStar_Syntax_Syntax.pos =
                (uu___225_14861.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___225_14861.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___226_14890 = comp1 in
            let uu____14893 =
              let uu____14894 =
                let uu____14903 = norm cfg env [] t in
                let uu____14904 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____14903, uu____14904) in
              FStar_Syntax_Syntax.GTotal uu____14894 in
            {
              FStar_Syntax_Syntax.n = uu____14893;
              FStar_Syntax_Syntax.pos =
                (uu___226_14890.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___226_14890.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____14956  ->
                      match uu____14956 with
                      | (a,i) ->
                          let uu____14967 = norm cfg env [] a in
                          (uu____14967, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___179_14978  ->
                      match uu___179_14978 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____14982 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____14982
                      | f -> f)) in
            let uu___227_14986 = comp1 in
            let uu____14989 =
              let uu____14990 =
                let uu___228_14991 = ct in
                let uu____14992 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____14993 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____14996 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____14992;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___228_14991.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____14993;
                  FStar_Syntax_Syntax.effect_args = uu____14996;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____14990 in
            {
              FStar_Syntax_Syntax.n = uu____14989;
              FStar_Syntax_Syntax.pos =
                (uu___227_14986.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___227_14986.FStar_Syntax_Syntax.vars)
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
            (let uu___229_15014 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___229_15014.tcenv);
               delta_level = (uu___229_15014.delta_level);
               primitive_steps = (uu___229_15014.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____15019 = norm1 t in
          FStar_Syntax_Util.non_informative uu____15019 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____15022 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___230_15041 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.pos =
                (uu___230_15041.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___230_15041.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____15048 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____15048
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
                    let uu___231_15059 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___231_15059.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___231_15059.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___231_15059.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___232_15061 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___232_15061.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___232_15061.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___232_15061.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___232_15061.FStar_Syntax_Syntax.flags)
                    } in
              let uu___233_15062 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos =
                  (uu___233_15062.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___233_15062.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____15064 -> c
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____15067  ->
        match uu____15067 with
        | (x,imp) ->
            let uu____15070 =
              let uu___234_15071 = x in
              let uu____15072 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___234_15071.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___234_15071.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____15072
              } in
            (uu____15070, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____15078 =
          FStar_List.fold_left
            (fun uu____15096  ->
               fun b  ->
                 match uu____15096 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____15078 with | (nbs,uu____15124) -> FStar_List.rev nbs
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
            let uu____15140 =
              let uu___235_15141 = rc in
              let uu____15142 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___235_15141.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____15142;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___235_15141.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____15140
        | uu____15149 -> lopt
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
              ((let uu____15162 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____15162
                then
                  let time_now = FStar_Util.now () in
                  let uu____15164 =
                    let uu____15165 =
                      let uu____15166 =
                        FStar_Util.time_diff time_then time_now in
                      FStar_Pervasives_Native.snd uu____15166 in
                    FStar_Util.string_of_int uu____15165 in
                  let uu____15171 = FStar_Syntax_Print.term_to_string tm in
                  let uu____15172 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                    uu____15164 uu____15171 uu____15172
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___236_15190 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___236_15190.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____15283  ->
                    let uu____15284 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____15284);
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
              let uu____15320 =
                let uu___237_15321 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___237_15321.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___237_15321.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____15320
          | (Arg (Univ uu____15322,uu____15323,uu____15324))::uu____15325 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____15328,uu____15329))::uu____15330 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____15346),aq,r))::stack2 ->
              (log cfg
                 (fun uu____15375  ->
                    let uu____15376 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____15376);
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
                 (let uu____15386 = FStar_ST.op_Bang m in
                  match uu____15386 with
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
                  | FStar_Pervasives_Native.Some (uu____15506,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq)
                          FStar_Pervasives_Native.None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 =
                FStar_Syntax_Syntax.extend_app head1 (t, aq)
                  FStar_Pervasives_Native.None r in
              let uu____15530 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____15530
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____15540  ->
                    let uu____15541 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____15541);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____15546 =
                  log cfg
                    (fun uu____15551  ->
                       let uu____15552 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____15553 =
                         let uu____15554 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____15571  ->
                                   match uu____15571 with
                                   | (p,uu____15581,uu____15582) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____15554
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____15552 uu____15553);
                  (let whnf1 = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___180_15599  ->
                               match uu___180_15599 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____15600 -> false)) in
                     let steps' =
                       let uu____15604 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____15604
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     only_strong_steps
                       (let uu___238_15610 = cfg in
                        {
                          steps = (FStar_List.append steps' cfg.steps);
                          tcenv = (uu___238_15610.tcenv);
                          delta_level = new_delta;
                          primitive_steps = (uu___238_15610.primitive_steps)
                        }) in
                   let norm_or_whnf env2 t1 =
                     if whnf1
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____15654 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____15677 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____15743  ->
                                   fun uu____15744  ->
                                     match (uu____15743, uu____15744) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____15847 = norm_pat env3 p1 in
                                         (match uu____15847 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____15677 with
                          | (pats1,env3) ->
                              ((let uu___239_15949 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.p =
                                    (uu___239_15949.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___240_15968 = x in
                           let uu____15969 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___240_15968.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___240_15968.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____15969
                           } in
                         ((let uu___241_15977 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.p =
                               (uu___241_15977.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___242_15982 = x in
                           let uu____15983 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___242_15982.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___242_15982.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____15983
                           } in
                         ((let uu___243_15991 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.p =
                               (uu___243_15991.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___244_16001 = x in
                           let uu____16002 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___244_16001.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___244_16001.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16002
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___245_16011 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.p =
                               (uu___245_16011.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf1 -> branches
                     | uu____16015 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____16029 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____16029 with
                                 | (p,wopt,e) ->
                                     let uu____16049 = norm_pat env1 p in
                                     (match uu____16049 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Pervasives_Native.Some w
                                                ->
                                                let uu____16080 =
                                                  norm_or_whnf env2 w in
                                                FStar_Pervasives_Native.Some
                                                  uu____16080 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____16086 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____16086) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____16096) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____16101 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____16102;
                        FStar_Syntax_Syntax.fv_delta = uu____16103;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Data_ctor );_}
                      -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____16104;
                        FStar_Syntax_Syntax.fv_delta = uu____16105;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Record_ctor uu____16106);_}
                      -> true
                  | uu____16113 -> false in
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
                  let uu____16242 =
                    FStar_Syntax_Util.head_and_args scrutinee1 in
                  match uu____16242 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var uu____16291 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_wild uu____16294 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____16297 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee1.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____16316 ->
                                let uu____16317 =
                                  let uu____16318 = is_cons head1 in
                                  Prims.op_Negation uu____16318 in
                                FStar_Util.Inr uu____16317)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____16339 =
                             let uu____16340 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____16340.FStar_Syntax_Syntax.n in
                           (match uu____16339 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____16350 ->
                                let uu____16351 =
                                  let uu____16352 = is_cons head1 in
                                  Prims.op_Negation uu____16352 in
                                FStar_Util.Inr uu____16351))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____16405)::rest_a,(p1,uu____16408)::rest_p) ->
                      let uu____16452 = matches_pat t1 p1 in
                      (match uu____16452 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____16477 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____16579 = matches_pat scrutinee1 p1 in
                      (match uu____16579 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____16599  ->
                                 let uu____16600 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____16601 =
                                   let uu____16602 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____16602
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____16600 uu____16601);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____16619 =
                                        let uu____16620 =
                                          let uu____16639 =
                                            FStar_Util.mk_ref
                                              (FStar_Pervasives_Native.Some
                                                 ([], t1)) in
                                          ([], t1, uu____16639, false) in
                                        Clos uu____16620 in
                                      uu____16619 :: env2) env1 s in
                             let uu____16692 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____16692))) in
                let uu____16693 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____16693
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___181_16716  ->
                match uu___181_16716 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____16720 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____16726 -> d in
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
            let uu___246_16755 = config s e in
            {
              steps = (uu___246_16755.steps);
              tcenv = (uu___246_16755.tcenv);
              delta_level = (uu___246_16755.delta_level);
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
      fun t  -> let uu____16780 = config s e in norm_comp uu____16780 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____16789 = config [] env in norm_universe uu____16789 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let uu____16798 = config [] env in ghost_to_pure_aux uu____16798 [] c
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
        let uu____16812 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____16812 in
      let uu____16813 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____16813
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___247_16815 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___247_16815.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___247_16815.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____16818  ->
                    let uu____16819 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____16819))
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
            ((let uu____16838 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning
                "Normalization failed with error %s\n" uu____16838);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____16851 = config [AllowUnboundUniverses] env in
          norm_comp uu____16851 [] c
        with
        | e ->
            ((let uu____16858 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning
                "Normalization failed with error %s\n" uu____16858);
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
                   let uu____16898 =
                     let uu____16899 =
                       let uu____16906 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____16906) in
                     FStar_Syntax_Syntax.Tm_refine uu____16899 in
                   mk uu____16898 t01.FStar_Syntax_Syntax.pos
               | uu____16911 -> t2)
          | uu____16912 -> t2 in
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
        let uu____16964 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____16964 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____16993 ->
                 let uu____17000 = FStar_Syntax_Util.abs_formals e in
                 (match uu____17000 with
                  | (actuals,uu____17010,uu____17011) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____17025 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____17025 with
                         | (binders,args) ->
                             let uu____17042 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____17042
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
      | uu____17052 ->
          let uu____17053 = FStar_Syntax_Util.head_and_args t in
          (match uu____17053 with
           | (head1,args) ->
               let uu____17090 =
                 let uu____17091 = FStar_Syntax_Subst.compress head1 in
                 uu____17091.FStar_Syntax_Syntax.n in
               (match uu____17090 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____17094,thead) ->
                    let uu____17120 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____17120 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____17162 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___252_17170 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___252_17170.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___252_17170.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___252_17170.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___252_17170.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___252_17170.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___252_17170.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___252_17170.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___252_17170.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___252_17170.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___252_17170.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___252_17170.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___252_17170.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___252_17170.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___252_17170.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___252_17170.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___252_17170.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___252_17170.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___252_17170.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___252_17170.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___252_17170.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___252_17170.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___252_17170.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___252_17170.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___252_17170.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___252_17170.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___252_17170.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___252_17170.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___252_17170.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___252_17170.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___252_17170.FStar_TypeChecker_Env.dsenv)
                                 }) t in
                            match uu____17162 with
                            | (uu____17171,ty,uu____17173) ->
                                eta_expand_with_type env t ty))
                | uu____17174 ->
                    let uu____17175 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___253_17183 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___253_17183.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___253_17183.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___253_17183.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___253_17183.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___253_17183.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___253_17183.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___253_17183.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___253_17183.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___253_17183.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___253_17183.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___253_17183.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___253_17183.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___253_17183.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___253_17183.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___253_17183.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___253_17183.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___253_17183.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___253_17183.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___253_17183.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___253_17183.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___253_17183.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___253_17183.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___253_17183.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___253_17183.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___253_17183.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___253_17183.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___253_17183.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___253_17183.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___253_17183.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___253_17183.FStar_TypeChecker_Env.dsenv)
                         }) t in
                    (match uu____17175 with
                     | (uu____17184,ty,uu____17186) ->
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
            | (uu____17264,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____17270,FStar_Util.Inl t) ->
                let uu____17276 =
                  let uu____17279 =
                    let uu____17280 =
                      let uu____17293 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____17293) in
                    FStar_Syntax_Syntax.Tm_arrow uu____17280 in
                  FStar_Syntax_Syntax.mk uu____17279 in
                uu____17276 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____17297 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____17297 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____17324 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____17379 ->
                    let uu____17380 =
                      let uu____17389 =
                        let uu____17390 = FStar_Syntax_Subst.compress t3 in
                        uu____17390.FStar_Syntax_Syntax.n in
                      (uu____17389, tc) in
                    (match uu____17380 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____17415) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____17452) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____17491,FStar_Util.Inl uu____17492) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____17515 -> failwith "Impossible") in
              (match uu____17324 with
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
          let uu____17624 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____17624 with
          | (univ_names1,binders1,tc) ->
              let uu____17682 = FStar_Util.left tc in
              (univ_names1, binders1, uu____17682)
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
          let uu____17721 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____17721 with
          | (univ_names1,binders1,tc) ->
              let uu____17781 = FStar_Util.right tc in
              (univ_names1, binders1, uu____17781)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____17816 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____17816 with
           | (univ_names1,binders1,typ1) ->
               let uu___254_17844 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___254_17844.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___254_17844.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___254_17844.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___254_17844.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___255_17865 = s in
          let uu____17866 =
            let uu____17867 =
              let uu____17876 = FStar_List.map (elim_uvars env) sigs in
              (uu____17876, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____17867 in
          {
            FStar_Syntax_Syntax.sigel = uu____17866;
            FStar_Syntax_Syntax.sigrng =
              (uu___255_17865.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___255_17865.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___255_17865.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___255_17865.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____17893 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____17893 with
           | (univ_names1,uu____17911,typ1) ->
               let uu___256_17925 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___256_17925.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___256_17925.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___256_17925.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___256_17925.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____17931 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____17931 with
           | (univ_names1,uu____17949,typ1) ->
               let uu___257_17963 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___257_17963.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___257_17963.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___257_17963.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___257_17963.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____17997 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____17997 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____18020 =
                            let uu____18021 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____18021 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____18020 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___258_18024 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___258_18024.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___258_18024.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___259_18025 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___259_18025.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___259_18025.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___259_18025.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___259_18025.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___260_18037 = s in
          let uu____18038 =
            let uu____18039 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____18039 in
          {
            FStar_Syntax_Syntax.sigel = uu____18038;
            FStar_Syntax_Syntax.sigrng =
              (uu___260_18037.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___260_18037.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___260_18037.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___260_18037.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____18043 = elim_uvars_aux_t env us [] t in
          (match uu____18043 with
           | (us1,uu____18061,t1) ->
               let uu___261_18075 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___261_18075.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___261_18075.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___261_18075.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___261_18075.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____18076 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____18078 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____18078 with
           | (univs1,binders,signature) ->
               let uu____18106 =
                 let uu____18115 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____18115 with
                 | (univs_opening,univs2) ->
                     let uu____18142 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____18142) in
               (match uu____18106 with
                | (univs_opening,univs_closing) ->
                    let uu____18159 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____18165 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____18166 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____18165, uu____18166) in
                    (match uu____18159 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____18188 =
                           match uu____18188 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____18206 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____18206 with
                                | (us1,t1) ->
                                    let uu____18217 =
                                      let uu____18222 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____18229 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____18222, uu____18229) in
                                    (match uu____18217 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____18242 =
                                           let uu____18247 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____18256 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____18247, uu____18256) in
                                         (match uu____18242 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____18272 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____18272 in
                                              let uu____18273 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____18273 with
                                               | (uu____18294,uu____18295,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____18310 =
                                                       let uu____18311 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____18311 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____18310 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____18316 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____18316 with
                           | (uu____18329,uu____18330,t1) -> t1 in
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
                             | uu____18390 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____18407 =
                               let uu____18408 =
                                 FStar_Syntax_Subst.compress body in
                               uu____18408.FStar_Syntax_Syntax.n in
                             match uu____18407 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____18467 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____18496 =
                               let uu____18497 =
                                 FStar_Syntax_Subst.compress t in
                               uu____18497.FStar_Syntax_Syntax.n in
                             match uu____18496 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____18518) ->
                                 let uu____18539 = destruct_action_body body in
                                 (match uu____18539 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____18584 ->
                                 let uu____18585 = destruct_action_body t in
                                 (match uu____18585 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____18634 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____18634 with
                           | (action_univs,t) ->
                               let uu____18643 = destruct_action_typ_templ t in
                               (match uu____18643 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___262_18684 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___262_18684.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___262_18684.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___263_18686 = ed in
                           let uu____18687 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____18688 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____18689 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____18690 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____18691 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____18692 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____18693 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____18694 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____18695 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____18696 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____18697 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____18698 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____18699 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____18700 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___263_18686.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___263_18686.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____18687;
                             FStar_Syntax_Syntax.bind_wp = uu____18688;
                             FStar_Syntax_Syntax.if_then_else = uu____18689;
                             FStar_Syntax_Syntax.ite_wp = uu____18690;
                             FStar_Syntax_Syntax.stronger = uu____18691;
                             FStar_Syntax_Syntax.close_wp = uu____18692;
                             FStar_Syntax_Syntax.assert_p = uu____18693;
                             FStar_Syntax_Syntax.assume_p = uu____18694;
                             FStar_Syntax_Syntax.null_wp = uu____18695;
                             FStar_Syntax_Syntax.trivial = uu____18696;
                             FStar_Syntax_Syntax.repr = uu____18697;
                             FStar_Syntax_Syntax.return_repr = uu____18698;
                             FStar_Syntax_Syntax.bind_repr = uu____18699;
                             FStar_Syntax_Syntax.actions = uu____18700
                           } in
                         let uu___264_18703 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___264_18703.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___264_18703.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___264_18703.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___264_18703.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___182_18720 =
            match uu___182_18720 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____18747 = elim_uvars_aux_t env us [] t in
                (match uu____18747 with
                 | (us1,uu____18771,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___265_18790 = sub_eff in
            let uu____18791 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____18794 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___265_18790.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___265_18790.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____18791;
              FStar_Syntax_Syntax.lift = uu____18794
            } in
          let uu___266_18797 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___266_18797.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___266_18797.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___266_18797.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___266_18797.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____18807 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____18807 with
           | (univ_names1,binders1,comp1) ->
               let uu___267_18841 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___267_18841.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___267_18841.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___267_18841.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___267_18841.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____18852 -> s