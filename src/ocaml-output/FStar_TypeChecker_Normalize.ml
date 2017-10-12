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
        let uu____5311 = FStar_Syntax_Embeddings.unembed_range r1 in
        FStar_Util.bind_opt uu____5311
          (fun r2  ->
             FStar_Pervasives_Native.Some
               (let uu___202_5321 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___202_5321.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r2;
                  FStar_Syntax_Syntax.vars =
                    (uu___202_5321.FStar_Syntax_Syntax.vars)
                }))
    | uu____5322 -> FStar_Pervasives_Native.None in
  let mk_range1 r args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____5401 =
          let uu____5422 = arg_as_string fn in
          let uu____5425 = arg_as_int from_line in
          let uu____5428 = arg_as_int from_col in
          let uu____5431 = arg_as_int to_line in
          let uu____5434 = arg_as_int to_col in
          (uu____5422, uu____5425, uu____5428, uu____5431, uu____5434) in
        (match uu____5401 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r1 =
               let uu____5465 = FStar_Range.mk_pos from_l from_c in
               let uu____5466 = FStar_Range.mk_pos to_l to_c in
               FStar_Range.mk_range fn1 uu____5465 uu____5466 in
             let uu____5467 = term_of_range r1 in
             FStar_Pervasives_Native.Some uu____5467
         | uu____5472 -> FStar_Pervasives_Native.None)
    | uu____5493 -> FStar_Pervasives_Native.None in
  let decidable_eq neg rng args =
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) rng in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) rng in
    match args with
    | (_typ,uu____5523)::(a1,uu____5525)::(a2,uu____5527)::[] ->
        let uu____5564 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____5564 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____5577 -> FStar_Pervasives_Native.None)
    | uu____5578 -> failwith "Unexpected number of arguments" in
  let basic_ops =
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
                                        let uu____5866 =
                                          let uu____5881 =
                                            let uu____5896 =
                                              let uu____5909 =
                                                FStar_Parser_Const.p2l
                                                  ["FStar";
                                                  "String";
                                                  "list_of_string"] in
                                              (uu____5909,
                                                (Prims.parse_int "1"),
                                                (unary_op arg_as_string
                                                   list_of_string')) in
                                            let uu____5916 =
                                              let uu____5931 =
                                                let uu____5944 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "string_of_list"] in
                                                (uu____5944,
                                                  (Prims.parse_int "1"),
                                                  (unary_op
                                                     (arg_as_list arg_as_char)
                                                     string_of_list')) in
                                              let uu____5953 =
                                                let uu____5968 =
                                                  let uu____5987 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "concat"] in
                                                  (uu____5987,
                                                    (Prims.parse_int "2"),
                                                    string_concat') in
                                                let uu____6000 =
                                                  let uu____6021 =
                                                    let uu____6042 =
                                                      FStar_Parser_Const.p2l
                                                        ["Prims"; "range_of"] in
                                                    (uu____6042,
                                                      (Prims.parse_int "2"),
                                                      range_of1) in
                                                  let uu____6057 =
                                                    let uu____6080 =
                                                      let uu____6099 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "set_range_of"] in
                                                      (uu____6099,
                                                        (Prims.parse_int "3"),
                                                        set_range_of1) in
                                                    let uu____6112 =
                                                      let uu____6133 =
                                                        let uu____6152 =
                                                          FStar_Parser_Const.p2l
                                                            ["Prims";
                                                            "mk_range"] in
                                                        (uu____6152,
                                                          (Prims.parse_int
                                                             "5"), mk_range1) in
                                                      [uu____6133] in
                                                    uu____6080 :: uu____6112 in
                                                  uu____6021 :: uu____6057 in
                                                uu____5968 :: uu____6000 in
                                              uu____5931 :: uu____5953 in
                                            uu____5896 :: uu____5916 in
                                          (FStar_Parser_Const.op_notEq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq true)) ::
                                            uu____5881 in
                                        (FStar_Parser_Const.op_Eq,
                                          (Prims.parse_int "3"),
                                          (decidable_eq false)) :: uu____5866 in
                                      (FStar_Parser_Const.string_compare,
                                        (Prims.parse_int "2"),
                                        (binary_op arg_as_string
                                           string_compare'))
                                        :: uu____5851 in
                                    (FStar_Parser_Const.string_of_bool_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_bool string_of_bool2))
                                      :: uu____5836 in
                                  (FStar_Parser_Const.string_of_int_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_int string_of_int2)) ::
                                    uu____5821 in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____5806 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5791 in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____5776 in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____5761 in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____5746 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____5731 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
                      :: uu____5716 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____5701 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____5686 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____5671 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____5656 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____5641 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____5626 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____5611 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____5596 in
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
      let uu____6757 =
        let uu____6758 =
          let uu____6759 = FStar_Syntax_Syntax.as_arg c in [uu____6759] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6758 in
      uu____6757 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____6794 =
              let uu____6807 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____6807, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____6826  ->
                        fun uu____6827  ->
                          match (uu____6826, uu____6827) with
                          | ((int_to_t1,x),(uu____6846,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____6856 =
              let uu____6871 =
                let uu____6884 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____6884, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____6903  ->
                          fun uu____6904  ->
                            match (uu____6903, uu____6904) with
                            | ((int_to_t1,x),(uu____6923,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____6933 =
                let uu____6948 =
                  let uu____6961 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____6961, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____6980  ->
                            fun uu____6981  ->
                              match (uu____6980, uu____6981) with
                              | ((int_to_t1,x),(uu____7000,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____6948] in
              uu____6871 :: uu____6933 in
            uu____6794 :: uu____6856)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop r args =
    match args with
    | (_typ,uu____7096)::(a1,uu____7098)::(a2,uu____7100)::[] ->
        let uu____7137 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____7137 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___203_7143 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___203_7143.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___203_7143.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___204_7147 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___204_7147.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___204_7147.FStar_Syntax_Syntax.vars)
                })
         | uu____7148 -> FStar_Pervasives_Native.None)
    | (_typ,uu____7150)::uu____7151::(a1,uu____7153)::(a2,uu____7155)::[] ->
        let uu____7204 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____7204 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___203_7210 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___203_7210.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___203_7210.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___204_7214 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___204_7214.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___204_7214.FStar_Syntax_Syntax.vars)
                })
         | uu____7215 -> FStar_Pervasives_Native.None)
    | uu____7216 -> failwith "Unexpected number of arguments" in
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
      let uu____7229 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops cfg.steps) in
      if uu____7229
      then tm
      else
        (let uu____7231 = FStar_Syntax_Util.head_and_args tm in
         match uu____7231 with
         | (head1,args) ->
             let uu____7268 =
               let uu____7269 = FStar_Syntax_Util.un_uinst head1 in
               uu____7269.FStar_Syntax_Syntax.n in
             (match uu____7268 with
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____7273 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps in
                  (match uu____7273 with
                   | FStar_Pervasives_Native.None  -> tm
                   | FStar_Pervasives_Native.Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then
                         (log cfg
                            (fun uu____7290  ->
                               let uu____7291 =
                                 FStar_Syntax_Print.lid_to_string
                                   prim_step.name in
                               let uu____7292 =
                                 FStar_Util.string_of_int
                                   (FStar_List.length args) in
                               let uu____7299 =
                                 FStar_Util.string_of_int prim_step.arity in
                               FStar_Util.print3
                                 "primop: found partially applied %s (%s/%s args)\n"
                                 uu____7291 uu____7292 uu____7299);
                          tm)
                       else
                         (log cfg
                            (fun uu____7304  ->
                               let uu____7305 =
                                 FStar_Syntax_Print.term_to_string tm in
                               FStar_Util.print1
                                 "primop: trying to reduce <%s>\n" uu____7305);
                          (let uu____7306 =
                             prim_step.interpretation
                               head1.FStar_Syntax_Syntax.pos args in
                           match uu____7306 with
                           | FStar_Pervasives_Native.None  ->
                               (log cfg
                                  (fun uu____7312  ->
                                     let uu____7313 =
                                       FStar_Syntax_Print.term_to_string tm in
                                     FStar_Util.print1
                                       "primop: <%s> did not reduce\n"
                                       uu____7313);
                                tm)
                           | FStar_Pervasives_Native.Some reduced ->
                               (log cfg
                                  (fun uu____7319  ->
                                     let uu____7320 =
                                       FStar_Syntax_Print.term_to_string tm in
                                     let uu____7321 =
                                       FStar_Syntax_Print.term_to_string
                                         reduced in
                                     FStar_Util.print2
                                       "primop: <%s> reduced to <%s>\n"
                                       uu____7320 uu____7321);
                                reduced))))
              | uu____7322 -> tm))
let reduce_equality:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___205_7333 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___205_7333.tcenv);
           delta_level = (uu___205_7333.delta_level);
           primitive_steps = equality_ops
         }) tm
let maybe_simplify:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      let tm1 = reduce_primops cfg tm in
      let uu____7343 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify cfg.steps) in
      if uu____7343
      then tm1
      else
        (let w t =
           let uu___206_7355 = t in
           {
             FStar_Syntax_Syntax.n = (uu___206_7355.FStar_Syntax_Syntax.n);
             FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
             FStar_Syntax_Syntax.vars =
               (uu___206_7355.FStar_Syntax_Syntax.vars)
           } in
         let simp_t t =
           match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
               -> FStar_Pervasives_Native.Some true
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
               -> FStar_Pervasives_Native.Some false
           | uu____7372 -> FStar_Pervasives_Native.None in
         let simplify1 arg =
           ((simp_t (FStar_Pervasives_Native.fst arg)), arg) in
         match tm1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.pos = uu____7412;
                     FStar_Syntax_Syntax.vars = uu____7413;_},uu____7414);
                FStar_Syntax_Syntax.pos = uu____7415;
                FStar_Syntax_Syntax.vars = uu____7416;_},args)
             ->
             let uu____7442 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
             if uu____7442
             then
               let uu____7443 =
                 FStar_All.pipe_right args (FStar_List.map simplify1) in
               (match uu____7443 with
                | (FStar_Pervasives_Native.Some (true ),uu____7498)::
                    (uu____7499,(arg,uu____7501))::[] -> arg
                | (uu____7566,(arg,uu____7568))::(FStar_Pervasives_Native.Some
                                                  (true ),uu____7569)::[]
                    -> arg
                | (FStar_Pervasives_Native.Some (false ),uu____7634)::uu____7635::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____7698::(FStar_Pervasives_Native.Some (false
                               ),uu____7699)::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____7762 -> tm1)
             else
               (let uu____7778 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
                if uu____7778
                then
                  let uu____7779 =
                    FStar_All.pipe_right args (FStar_List.map simplify1) in
                  match uu____7779 with
                  | (FStar_Pervasives_Native.Some (true ),uu____7834)::uu____7835::[]
                      -> w FStar_Syntax_Util.t_true
                  | uu____7898::(FStar_Pervasives_Native.Some (true
                                 ),uu____7899)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____7962)::
                      (uu____7963,(arg,uu____7965))::[] -> arg
                  | (uu____8030,(arg,uu____8032))::(FStar_Pervasives_Native.Some
                                                    (false ),uu____8033)::[]
                      -> arg
                  | uu____8098 -> tm1
                else
                  (let uu____8114 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.imp_lid in
                   if uu____8114
                   then
                     let uu____8115 =
                       FStar_All.pipe_right args (FStar_List.map simplify1) in
                     match uu____8115 with
                     | uu____8170::(FStar_Pervasives_Native.Some (true
                                    ),uu____8171)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____8234)::uu____8235::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____8298)::
                         (uu____8299,(arg,uu____8301))::[] -> arg
                     | (uu____8366,(p,uu____8368))::(uu____8369,(q,uu____8371))::[]
                         ->
                         let uu____8436 = FStar_Syntax_Util.term_eq p q in
                         (if uu____8436
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____8438 -> tm1
                   else
                     (let uu____8454 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____8454
                      then
                        let uu____8455 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1) in
                        match uu____8455 with
                        | (FStar_Pervasives_Native.Some (true ),uu____8510)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____8549)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____8588 -> tm1
                      else
                        (let uu____8604 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____8604
                         then
                           match args with
                           | (t,uu____8606)::[] ->
                               let uu____8623 =
                                 let uu____8624 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____8624.FStar_Syntax_Syntax.n in
                               (match uu____8623 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____8627::[],body,uu____8629) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____8656 -> tm1)
                                | uu____8659 -> tm1)
                           | (uu____8660,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____8661))::
                               (t,uu____8663)::[] ->
                               let uu____8702 =
                                 let uu____8703 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____8703.FStar_Syntax_Syntax.n in
                               (match uu____8702 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____8706::[],body,uu____8708) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____8735 -> tm1)
                                | uu____8738 -> tm1)
                           | uu____8739 -> tm1
                         else
                           (let uu____8749 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____8749
                            then
                              match args with
                              | (t,uu____8751)::[] ->
                                  let uu____8768 =
                                    let uu____8769 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____8769.FStar_Syntax_Syntax.n in
                                  (match uu____8768 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____8772::[],body,uu____8774) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____8801 -> tm1)
                                   | uu____8804 -> tm1)
                              | (uu____8805,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____8806))::
                                  (t,uu____8808)::[] ->
                                  let uu____8847 =
                                    let uu____8848 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____8848.FStar_Syntax_Syntax.n in
                                  (match uu____8847 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____8851::[],body,uu____8853) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____8880 -> tm1)
                                   | uu____8883 -> tm1)
                              | uu____8884 -> tm1
                            else reduce_equality cfg tm1)))))
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                FStar_Syntax_Syntax.pos = uu____8895;
                FStar_Syntax_Syntax.vars = uu____8896;_},args)
             ->
             let uu____8918 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
             if uu____8918
             then
               let uu____8919 =
                 FStar_All.pipe_right args (FStar_List.map simplify1) in
               (match uu____8919 with
                | (FStar_Pervasives_Native.Some (true ),uu____8974)::
                    (uu____8975,(arg,uu____8977))::[] -> arg
                | (uu____9042,(arg,uu____9044))::(FStar_Pervasives_Native.Some
                                                  (true ),uu____9045)::[]
                    -> arg
                | (FStar_Pervasives_Native.Some (false ),uu____9110)::uu____9111::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____9174::(FStar_Pervasives_Native.Some (false
                               ),uu____9175)::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____9238 -> tm1)
             else
               (let uu____9254 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
                if uu____9254
                then
                  let uu____9255 =
                    FStar_All.pipe_right args (FStar_List.map simplify1) in
                  match uu____9255 with
                  | (FStar_Pervasives_Native.Some (true ),uu____9310)::uu____9311::[]
                      -> w FStar_Syntax_Util.t_true
                  | uu____9374::(FStar_Pervasives_Native.Some (true
                                 ),uu____9375)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____9438)::
                      (uu____9439,(arg,uu____9441))::[] -> arg
                  | (uu____9506,(arg,uu____9508))::(FStar_Pervasives_Native.Some
                                                    (false ),uu____9509)::[]
                      -> arg
                  | uu____9574 -> tm1
                else
                  (let uu____9590 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.imp_lid in
                   if uu____9590
                   then
                     let uu____9591 =
                       FStar_All.pipe_right args (FStar_List.map simplify1) in
                     match uu____9591 with
                     | uu____9646::(FStar_Pervasives_Native.Some (true
                                    ),uu____9647)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____9710)::uu____9711::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____9774)::
                         (uu____9775,(arg,uu____9777))::[] -> arg
                     | (uu____9842,(p,uu____9844))::(uu____9845,(q,uu____9847))::[]
                         ->
                         let uu____9912 = FStar_Syntax_Util.term_eq p q in
                         (if uu____9912
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____9914 -> tm1
                   else
                     (let uu____9930 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____9930
                      then
                        let uu____9931 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1) in
                        match uu____9931 with
                        | (FStar_Pervasives_Native.Some (true ),uu____9986)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____10025)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____10064 -> tm1
                      else
                        (let uu____10080 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____10080
                         then
                           match args with
                           | (t,uu____10082)::[] ->
                               let uu____10099 =
                                 let uu____10100 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____10100.FStar_Syntax_Syntax.n in
                               (match uu____10099 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____10103::[],body,uu____10105) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____10132 -> tm1)
                                | uu____10135 -> tm1)
                           | (uu____10136,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____10137))::
                               (t,uu____10139)::[] ->
                               let uu____10178 =
                                 let uu____10179 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____10179.FStar_Syntax_Syntax.n in
                               (match uu____10178 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____10182::[],body,uu____10184) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____10211 -> tm1)
                                | uu____10214 -> tm1)
                           | uu____10215 -> tm1
                         else
                           (let uu____10225 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____10225
                            then
                              match args with
                              | (t,uu____10227)::[] ->
                                  let uu____10244 =
                                    let uu____10245 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____10245.FStar_Syntax_Syntax.n in
                                  (match uu____10244 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____10248::[],body,uu____10250) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____10277 -> tm1)
                                   | uu____10280 -> tm1)
                              | (uu____10281,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____10282))::
                                  (t,uu____10284)::[] ->
                                  let uu____10323 =
                                    let uu____10324 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____10324.FStar_Syntax_Syntax.n in
                                  (match uu____10323 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____10327::[],body,uu____10329) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____10356 -> tm1)
                                   | uu____10359 -> tm1)
                              | uu____10360 -> tm1
                            else reduce_equality cfg tm1)))))
         | uu____10370 -> tm1)
let is_norm_request:
  'Auu____10377 .
    FStar_Syntax_Syntax.term -> 'Auu____10377 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10390 =
        let uu____10397 =
          let uu____10398 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10398.FStar_Syntax_Syntax.n in
        (uu____10397, args) in
      match uu____10390 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10404::uu____10405::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10409::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10414::uu____10415::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10418 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___173_10430  ->
    match uu___173_10430 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.WHNF  -> [WHNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10436 =
          let uu____10439 =
            let uu____10440 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____10440 in
          [uu____10439] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10436
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____10459 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10459) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10497 =
          let uu____10500 =
            FStar_Syntax_Embeddings.unembed_list
              FStar_Syntax_Embeddings.unembed_norm_step s in
          FStar_All.pipe_right uu____10500 FStar_Util.must in
        FStar_All.pipe_right uu____10497 tr_norm_steps in
      match args with
      | uu____10523::(tm,uu____10525)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____10548)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____10563)::uu____10564::(tm,uu____10566)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____10606 =
              let uu____10609 = full_norm steps in parse_steps uu____10609 in
            Beta :: uu____10606 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____10618 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___174_10636  ->
    match uu___174_10636 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.pos = uu____10639;
           FStar_Syntax_Syntax.vars = uu____10640;_},uu____10641,uu____10642))::uu____10643
        -> true
    | uu____10650 -> false
let should_reify: cfg -> stack_elt Prims.list -> Prims.bool =
  fun cfg  ->
    fun stack1  ->
      match stack1 with
      | (App
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify );
             FStar_Syntax_Syntax.pos = uu____10665;
             FStar_Syntax_Syntax.vars = uu____10666;_},uu____10667,uu____10668))::uu____10669
          -> FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)
      | uu____10676 -> false
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
            (fun uu____10823  ->
               let uu____10824 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____10825 = FStar_Syntax_Print.term_to_string t1 in
               let uu____10826 =
                 let uu____10827 =
                   let uu____10830 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____10830 in
                 stack_to_string uu____10827 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____10824
                 uu____10825 uu____10826);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____10853 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____10878 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____10895 =
                 let uu____10896 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____10897 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____10896 uu____10897 in
               failwith uu____10895
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____10898 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____10915 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____10916 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10917;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____10918;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10921;
                 FStar_Syntax_Syntax.fv_delta = uu____10922;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10923;
                 FStar_Syntax_Syntax.fv_delta = uu____10924;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____10925);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar fv when
               let uu____10933 = FStar_Syntax_Syntax.lid_of_fv fv in
               FStar_TypeChecker_Env.is_action cfg.tcenv uu____10933 ->
               let b = should_reify cfg stack1 in
               (log cfg
                  (fun uu____10939  ->
                     let uu____10940 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____10941 = FStar_Util.string_of_bool b in
                     FStar_Util.print2
                       ">>> For DM4F action %s, should_reify = %s\n"
                       uu____10940 uu____10941);
                if b
                then
                  (let uu____10942 = FStar_List.tl stack1 in
                   do_unfold_fv cfg env uu____10942 t1 fv)
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
                 let uu___207_10981 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___207_10981.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___207_10981.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____11014 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____11014) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___208_11022 = cfg in
                 let uu____11023 =
                   FStar_List.filter
                     (fun uu___175_11026  ->
                        match uu___175_11026 with
                        | UnfoldOnly uu____11027 -> false
                        | NoDeltaSteps  -> false
                        | uu____11030 -> true) cfg.steps in
                 {
                   steps = uu____11023;
                   tcenv = (uu___208_11022.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___208_11022.primitive_steps)
                 } in
               let uu____11031 = get_norm_request (norm cfg' env []) args in
               (match uu____11031 with
                | (s,tm) ->
                    let delta_level =
                      let uu____11047 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___176_11052  ->
                                match uu___176_11052 with
                                | UnfoldUntil uu____11053 -> true
                                | UnfoldOnly uu____11054 -> true
                                | uu____11057 -> false)) in
                      if uu____11047
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___209_11062 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___209_11062.tcenv);
                        delta_level;
                        primitive_steps = (uu___209_11062.primitive_steps)
                      } in
                    let stack' =
                      let tail1 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let uu____11073 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____11073
                      then
                        let uu____11076 =
                          let uu____11077 =
                            let uu____11082 = FStar_Util.now () in
                            (t1, uu____11082) in
                          Debug uu____11077 in
                        uu____11076 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11084;
                  FStar_Syntax_Syntax.vars = uu____11085;_},a1::a2::rest)
               ->
               let uu____11133 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11133 with
                | (hd1,uu____11149) ->
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
                    (FStar_Const.Const_reflect uu____11214);
                  FStar_Syntax_Syntax.pos = uu____11215;
                  FStar_Syntax_Syntax.vars = uu____11216;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____11248 = FStar_List.tl stack1 in
               norm cfg env uu____11248 (FStar_Pervasives_Native.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11251;
                  FStar_Syntax_Syntax.vars = uu____11252;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____11284 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11284 with
                | (reify_head,uu____11300) ->
                    let a1 =
                      let uu____11322 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (FStar_Pervasives_Native.fst a) in
                      FStar_Syntax_Subst.compress uu____11322 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____11325);
                            FStar_Syntax_Syntax.pos = uu____11326;
                            FStar_Syntax_Syntax.vars = uu____11327;_},a2::[])
                         ->
                         norm cfg env stack1 (FStar_Pervasives_Native.fst a2)
                     | uu____11361 ->
                         let stack2 =
                           (App
                              (reify_head, FStar_Pervasives_Native.None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11371 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____11371
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11378 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11378
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____11381 =
                      let uu____11388 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11388, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11381 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___177_11401  ->
                         match uu___177_11401 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11404 =
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
                 if uu____11404
                 then false
                 else
                   (let uu____11406 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___178_11413  ->
                              match uu___178_11413 with
                              | UnfoldOnly uu____11414 -> true
                              | uu____11417 -> false)) in
                    match uu____11406 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11421 -> should_delta) in
               (log cfg
                  (fun uu____11429  ->
                     let uu____11430 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11431 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____11432 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11430 uu____11431 uu____11432);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack1 t1
                else do_unfold_fv cfg env stack1 t1 f)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11435 = lookup_bvar env x in
               (match uu____11435 with
                | Univ uu____11436 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11461 = FStar_ST.op_Bang r in
                      (match uu____11461 with
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
                      (let uu___210_11738 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___210_11738.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____11823  ->
                          let uu____11824 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11824);
                     norm cfg env stack2 t1)
                | (Debug uu____11825)::uu____11826 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11833 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11833
                    else
                      (let uu____11835 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11835 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11859  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11875 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11875
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11885 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11885)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___211_11890 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___211_11890.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___211_11890.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11891 -> lopt in
                           (log cfg
                              (fun uu____11897  ->
                                 let uu____11898 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11898);
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
                | (Meta uu____11915)::uu____11916 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11923 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11923
                    else
                      (let uu____11925 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11925 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11949  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11965 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11965
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11975 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11975)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___211_11980 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___211_11980.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___211_11980.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11981 -> lopt in
                           (log cfg
                              (fun uu____11987  ->
                                 let uu____11988 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11988);
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
                | (Let uu____12005)::uu____12006 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12017 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12017
                    else
                      (let uu____12019 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12019 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12043  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12059 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12059
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12069 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12069)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___211_12074 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___211_12074.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___211_12074.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12075 -> lopt in
                           (log cfg
                              (fun uu____12081  ->
                                 let uu____12082 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12082);
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
                | (App uu____12099)::uu____12100 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12109 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12109
                    else
                      (let uu____12111 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12111 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12135  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12151 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12151
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12161 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12161)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___211_12166 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___211_12166.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___211_12166.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12167 -> lopt in
                           (log cfg
                              (fun uu____12173  ->
                                 let uu____12174 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12174);
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
                                   (let uu___211_12264 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___211_12264.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___211_12264.FStar_Syntax_Syntax.residual_flags)
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
                             let cfg1 = only_strong_steps cfg in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12289 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12289
                    else
                      (let uu____12291 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12291 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12315  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12331 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12331
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12341 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12341)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___211_12346 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___211_12346.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___211_12346.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12347 -> lopt in
                           (log cfg
                              (fun uu____12353  ->
                                 let uu____12354 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12354);
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
                      (fun uu____12409  ->
                         fun stack2  ->
                           match uu____12409 with
                           | (a,aq) ->
                               let uu____12421 =
                                 let uu____12422 =
                                   let uu____12429 =
                                     let uu____12430 =
                                       let uu____12449 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____12449, false) in
                                     Clos uu____12430 in
                                   (uu____12429, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____12422 in
                               uu____12421 :: stack2) args) in
               (log cfg
                  (fun uu____12501  ->
                     let uu____12502 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12502);
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
                             ((let uu___212_12526 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___212_12526.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___212_12526.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____12527 ->
                      let uu____12532 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12532)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____12535 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____12535 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____12560 =
                          let uu____12561 =
                            let uu____12568 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___213_12570 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___213_12570.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___213_12570.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12568) in
                          FStar_Syntax_Syntax.Tm_refine uu____12561 in
                        mk uu____12560 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____12589 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____12589
               else
                 (let uu____12591 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____12591 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12599 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12611  -> Dummy :: env1) env) in
                        norm_comp cfg uu____12599 c1 in
                      let t2 =
                        let uu____12621 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____12621 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____12680)::uu____12681 -> norm cfg env stack1 t11
                | (Arg uu____12690)::uu____12691 -> norm cfg env stack1 t11
                | (App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____12700;
                       FStar_Syntax_Syntax.vars = uu____12701;_},uu____12702,uu____12703))::uu____12704
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____12711)::uu____12712 ->
                    norm cfg env stack1 t11
                | uu____12721 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____12725  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____12742 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____12742
                        | FStar_Util.Inr c ->
                            let uu____12750 = norm_comp cfg env c in
                            FStar_Util.Inr uu____12750 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____12756 =
                        let uu____12757 =
                          let uu____12758 =
                            let uu____12785 = FStar_Syntax_Util.unascribe t12 in
                            (uu____12785, (tc1, tacopt1), l) in
                          FStar_Syntax_Syntax.Tm_ascribed uu____12758 in
                        mk uu____12757 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____12756)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____12861,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____12862;
                               FStar_Syntax_Syntax.lbunivs = uu____12863;
                               FStar_Syntax_Syntax.lbtyp = uu____12864;
                               FStar_Syntax_Syntax.lbeff = uu____12865;
                               FStar_Syntax_Syntax.lbdef = uu____12866;_}::uu____12867),uu____12868)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____12904 =
                 (let uu____12907 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____12907) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____12909 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____12909))) in
               if uu____12904
               then
                 let env1 =
                   let uu____12913 =
                     let uu____12914 =
                       let uu____12933 =
                         FStar_Util.mk_ref FStar_Pervasives_Native.None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____12933,
                         false) in
                     Clos uu____12914 in
                   uu____12913 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____12985 =
                    let uu____12990 =
                      let uu____12991 =
                        let uu____12992 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____12992
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____12991] in
                    FStar_Syntax_Subst.open_term uu____12990 body in
                  match uu____12985 with
                  | (bs,body1) ->
                      let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                      let lbname =
                        let x =
                          let uu____13006 = FStar_List.hd bs in
                          FStar_Pervasives_Native.fst uu____13006 in
                        FStar_Util.Inl
                          (let uu___214_13016 = x in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___214_13016.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___214_13016.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = ty
                           }) in
                      let lb1 =
                        let uu___215_13018 = lb in
                        let uu____13019 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = lbname;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___215_13018.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = ty;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___215_13018.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____13019
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____13036  -> Dummy :: env1)
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
               let uu____13060 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____13060 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____13096 =
                               let uu___216_13097 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___216_13097.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___216_13097.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____13096 in
                           let uu____13098 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____13098 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____13118 =
                                   FStar_List.map (fun uu____13122  -> Dummy)
                                     lbs1 in
                                 let uu____13123 =
                                   let uu____13126 =
                                     FStar_List.map
                                       (fun uu____13134  -> Dummy) xs1 in
                                   FStar_List.append uu____13126 env in
                                 FStar_List.append uu____13118 uu____13123 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13146 =
                                       let uu___217_13147 = rc in
                                       let uu____13148 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___217_13147.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13148;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___217_13147.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____13146
                                 | uu____13155 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___218_13159 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___218_13159.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___218_13159.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____13163 =
                        FStar_List.map (fun uu____13167  -> Dummy) lbs2 in
                      FStar_List.append uu____13163 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____13169 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____13169 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___219_13185 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___219_13185.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___219_13185.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____13212 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____13212
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13231 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13282  ->
                        match uu____13282 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____13355 =
                                let uu___220_13356 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___220_13356.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___220_13356.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____13355 in
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
               (match uu____13231 with
                | (rec_env,memos,uu____13484) ->
                    let uu____13513 =
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
                             let uu____13978 =
                               let uu____13979 =
                                 let uu____13998 =
                                   FStar_Util.mk_ref
                                     FStar_Pervasives_Native.None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____13998, false) in
                               Clos uu____13979 in
                             uu____13978 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
                    norm cfg body_env stack1 body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (match m with
                | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                    let uu____14065 =
                      let uu____14066 = should_reify cfg stack1 in
                      Prims.op_Negation uu____14066 in
                    if uu____14065
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____14076 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____14076
                        then
                          let uu___221_14077 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___221_14077.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps =
                              (uu___221_14077.primitive_steps)
                          }
                        else
                          (let uu___222_14079 = cfg in
                           {
                             steps =
                               (FStar_List.append [Exclude Zeta] cfg.steps);
                             tcenv = (uu___222_14079.tcenv);
                             delta_level = (uu___222_14079.delta_level);
                             primitive_steps =
                               (uu___222_14079.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____14081 =
                         let uu____14082 = FStar_Syntax_Subst.compress head1 in
                         uu____14082.FStar_Syntax_Syntax.n in
                       match uu____14081 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____14100 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____14100 with
                            | (uu____14101,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____14107 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____14115 =
                                         let uu____14116 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____14116.FStar_Syntax_Syntax.n in
                                       match uu____14115 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____14122,uu____14123))
                                           ->
                                           let uu____14132 =
                                             let uu____14133 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____14133.FStar_Syntax_Syntax.n in
                                           (match uu____14132 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____14139,msrc,uu____14141))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____14150 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14150
                                            | uu____14151 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____14152 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____14153 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____14153 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___223_14158 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___223_14158.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___223_14158.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___223_14158.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____14159 =
                                            FStar_List.tl stack1 in
                                          let uu____14160 =
                                            let uu____14161 =
                                              let uu____14164 =
                                                let uu____14165 =
                                                  let uu____14178 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____14178) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____14165 in
                                              FStar_Syntax_Syntax.mk
                                                uu____14164 in
                                            uu____14161
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____14159
                                            uu____14160
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____14194 =
                                            let uu____14195 = is_return body in
                                            match uu____14195 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____14199;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____14200;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____14205 -> false in
                                          if uu____14194
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
                                               let uu____14229 =
                                                 let uu____14232 =
                                                   let uu____14233 =
                                                     let uu____14250 =
                                                       let uu____14253 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____14253] in
                                                     (uu____14250, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc)) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____14233 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____14232 in
                                               uu____14229
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____14269 =
                                                 let uu____14270 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____14270.FStar_Syntax_Syntax.n in
                                               match uu____14269 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____14276::uu____14277::[])
                                                   ->
                                                   let uu____14284 =
                                                     let uu____14287 =
                                                       let uu____14288 =
                                                         let uu____14295 =
                                                           let uu____14298 =
                                                             let uu____14299
                                                               =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____14299 in
                                                           let uu____14300 =
                                                             let uu____14303
                                                               =
                                                               let uu____14304
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____14304 in
                                                             [uu____14303] in
                                                           uu____14298 ::
                                                             uu____14300 in
                                                         (bind1, uu____14295) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____14288 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____14287 in
                                                   uu____14284
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____14312 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____14318 =
                                                 let uu____14321 =
                                                   let uu____14322 =
                                                     let uu____14337 =
                                                       let uu____14340 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____14341 =
                                                         let uu____14344 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____14345 =
                                                           let uu____14348 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____14349 =
                                                             let uu____14352
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____14353
                                                               =
                                                               let uu____14356
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____14357
                                                                 =
                                                                 let uu____14360
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____14360] in
                                                               uu____14356 ::
                                                                 uu____14357 in
                                                             uu____14352 ::
                                                               uu____14353 in
                                                           uu____14348 ::
                                                             uu____14349 in
                                                         uu____14344 ::
                                                           uu____14345 in
                                                       uu____14340 ::
                                                         uu____14341 in
                                                     (bind_inst, uu____14337) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____14322 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____14321 in
                                               uu____14318
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____14368 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____14368 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____14392 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____14392 with
                            | (uu____14393,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____14428 =
                                        let uu____14429 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____14429.FStar_Syntax_Syntax.n in
                                      match uu____14428 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____14435) -> t4
                                      | uu____14440 -> head2 in
                                    let uu____14441 =
                                      let uu____14442 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____14442.FStar_Syntax_Syntax.n in
                                    match uu____14441 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____14448 ->
                                        FStar_Pervasives_Native.None in
                                  let uu____14449 = maybe_extract_fv head2 in
                                  match uu____14449 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____14459 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____14459
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____14464 =
                                          maybe_extract_fv head3 in
                                        match uu____14464 with
                                        | FStar_Pervasives_Native.Some
                                            uu____14469 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____14470 ->
                                            FStar_Pervasives_Native.Some
                                              false in
                                      (head3, action_unfolded)
                                  | uu____14475 ->
                                      (head2, FStar_Pervasives_Native.None) in
                                ((let is_arg_impure uu____14490 =
                                    match uu____14490 with
                                    | (e,q) ->
                                        let uu____14497 =
                                          let uu____14498 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____14498.FStar_Syntax_Syntax.n in
                                        (match uu____14497 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____14513 -> false) in
                                  let uu____14514 =
                                    let uu____14515 =
                                      let uu____14522 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____14522 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____14515 in
                                  if uu____14514
                                  then
                                    let uu____14527 =
                                      let uu____14528 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____14528 in
                                    failwith uu____14527
                                  else ());
                                 (let uu____14530 =
                                    maybe_unfold_action head_app in
                                  match uu____14530 with
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
                                      let uu____14569 = FStar_List.tl stack1 in
                                      norm cfg env uu____14569 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____14583 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____14583 in
                           let uu____14584 = FStar_List.tl stack1 in
                           norm cfg env uu____14584 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____14705  ->
                                     match uu____14705 with
                                     | (pat,wopt,tm) ->
                                         let uu____14753 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____14753))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____14785 = FStar_List.tl stack1 in
                           norm cfg env uu____14785 tm
                       | uu____14786 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let uu____14794 = should_reify cfg stack1 in
                    if uu____14794
                    then
                      let uu____14795 = FStar_List.tl stack1 in
                      let uu____14796 =
                        let uu____14797 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____14797 in
                      norm cfg env uu____14795 uu____14796
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____14800 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____14800
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___224_14809 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___224_14809.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___224_14809.primitive_steps)
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
                | uu____14811 ->
                    if FStar_List.contains Unmeta cfg.steps
                    then norm cfg env stack1 head1
                    else
                      (match stack1 with
                       | uu____14813::uu____14814 ->
                           (match m with
                            | FStar_Syntax_Syntax.Meta_labeled
                                (l,r,uu____14819) ->
                                norm cfg env ((Meta (m, r)) :: stack1) head1
                            | FStar_Syntax_Syntax.Meta_alien uu____14820 ->
                                rebuild cfg env stack1 t1
                            | FStar_Syntax_Syntax.Meta_pattern args ->
                                let args1 = norm_pattern_args cfg env args in
                                norm cfg env
                                  ((Meta
                                      ((FStar_Syntax_Syntax.Meta_pattern
                                          args1),
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) head1
                            | uu____14851 -> norm cfg env stack1 head1)
                       | [] ->
                           let head2 = norm cfg env [] head1 in
                           let m1 =
                             match m with
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let uu____14865 =
                                   norm_pattern_args cfg env args in
                                 FStar_Syntax_Syntax.Meta_pattern uu____14865
                             | uu____14876 -> m in
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
              let uu____14888 = FStar_Syntax_Syntax.range_of_fv f in
              FStar_TypeChecker_Env.set_range cfg.tcenv uu____14888 in
            let uu____14889 =
              FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            match uu____14889 with
            | FStar_Pervasives_Native.None  ->
                (log cfg
                   (fun uu____14902  ->
                      FStar_Util.print "Tm_fvar case 2\n" []);
                 rebuild cfg env stack1 t0)
            | FStar_Pervasives_Native.Some (us,t) ->
                (log cfg
                   (fun uu____14913  ->
                      let uu____14914 = FStar_Syntax_Print.term_to_string t0 in
                      let uu____14915 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____14914
                        uu____14915);
                 (let t1 =
                    let uu____14917 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.contains
                           (UnfoldUntil FStar_Syntax_Syntax.Delta_constant)) in
                    if uu____14917
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
                    | (UnivArgs (us',uu____14927))::stack2 ->
                        let env1 =
                          FStar_All.pipe_right us'
                            (FStar_List.fold_left
                               (fun env1  -> fun u  -> (Univ u) :: env1) env) in
                        norm cfg env1 stack2 t1
                    | uu____14950 when
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains EraseUniverses)
                        -> norm cfg env stack1 t1
                    | uu____14953 ->
                        let uu____14956 =
                          let uu____14957 =
                            FStar_Syntax_Print.lid_to_string
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                          FStar_Util.format1
                            "Impossible: missing universe instantiation on %s"
                            uu____14957 in
                        failwith uu____14956
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
              let uu____14967 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____14967 with
              | (uu____14968,return_repr) ->
                  let return_inst =
                    let uu____14977 =
                      let uu____14978 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____14978.FStar_Syntax_Syntax.n in
                    match uu____14977 with
                    | FStar_Syntax_Syntax.Tm_uinst
                        (return_tm,uu____14984::[]) ->
                        let uu____14991 =
                          let uu____14994 =
                            let uu____14995 =
                              let uu____15002 =
                                let uu____15005 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____15005] in
                              (return_tm, uu____15002) in
                            FStar_Syntax_Syntax.Tm_uinst uu____14995 in
                          FStar_Syntax_Syntax.mk uu____14994 in
                        uu____14991 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____15013 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____15016 =
                    let uu____15019 =
                      let uu____15020 =
                        let uu____15035 =
                          let uu____15038 = FStar_Syntax_Syntax.as_arg t in
                          let uu____15039 =
                            let uu____15042 = FStar_Syntax_Syntax.as_arg e in
                            [uu____15042] in
                          uu____15038 :: uu____15039 in
                        (return_inst, uu____15035) in
                      FStar_Syntax_Syntax.Tm_app uu____15020 in
                    FStar_Syntax_Syntax.mk uu____15019 in
                  uu____15016 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____15051 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____15051 with
               | FStar_Pervasives_Native.None  ->
                   let uu____15054 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____15054
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____15055;
                     FStar_TypeChecker_Env.mtarget = uu____15056;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____15057;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____15068;
                     FStar_TypeChecker_Env.mtarget = uu____15069;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____15070;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____15088 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____15088)
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
                (fun uu____15144  ->
                   match uu____15144 with
                   | (a,imp) ->
                       let uu____15155 = norm cfg env [] a in
                       (uu____15155, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___225_15172 = comp1 in
            let uu____15175 =
              let uu____15176 =
                let uu____15185 = norm cfg env [] t in
                let uu____15186 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____15185, uu____15186) in
              FStar_Syntax_Syntax.Total uu____15176 in
            {
              FStar_Syntax_Syntax.n = uu____15175;
              FStar_Syntax_Syntax.pos =
                (uu___225_15172.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___225_15172.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___226_15201 = comp1 in
            let uu____15204 =
              let uu____15205 =
                let uu____15214 = norm cfg env [] t in
                let uu____15215 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____15214, uu____15215) in
              FStar_Syntax_Syntax.GTotal uu____15205 in
            {
              FStar_Syntax_Syntax.n = uu____15204;
              FStar_Syntax_Syntax.pos =
                (uu___226_15201.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___226_15201.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____15267  ->
                      match uu____15267 with
                      | (a,i) ->
                          let uu____15278 = norm cfg env [] a in
                          (uu____15278, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___179_15289  ->
                      match uu___179_15289 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____15293 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____15293
                      | f -> f)) in
            let uu___227_15297 = comp1 in
            let uu____15300 =
              let uu____15301 =
                let uu___228_15302 = ct in
                let uu____15303 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____15304 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____15307 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____15303;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___228_15302.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____15304;
                  FStar_Syntax_Syntax.effect_args = uu____15307;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____15301 in
            {
              FStar_Syntax_Syntax.n = uu____15300;
              FStar_Syntax_Syntax.pos =
                (uu___227_15297.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___227_15297.FStar_Syntax_Syntax.vars)
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
            (let uu___229_15325 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___229_15325.tcenv);
               delta_level = (uu___229_15325.delta_level);
               primitive_steps = (uu___229_15325.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____15330 = norm1 t in
          FStar_Syntax_Util.non_informative uu____15330 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____15333 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___230_15352 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.pos =
                (uu___230_15352.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___230_15352.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____15359 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____15359
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
                    let uu___231_15370 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___231_15370.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___231_15370.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___231_15370.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___232_15372 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___232_15372.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___232_15372.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___232_15372.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___232_15372.FStar_Syntax_Syntax.flags)
                    } in
              let uu___233_15373 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos =
                  (uu___233_15373.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___233_15373.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____15375 -> c
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____15378  ->
        match uu____15378 with
        | (x,imp) ->
            let uu____15381 =
              let uu___234_15382 = x in
              let uu____15383 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___234_15382.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___234_15382.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____15383
              } in
            (uu____15381, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____15389 =
          FStar_List.fold_left
            (fun uu____15407  ->
               fun b  ->
                 match uu____15407 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____15389 with | (nbs,uu____15435) -> FStar_List.rev nbs
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
            let uu____15451 =
              let uu___235_15452 = rc in
              let uu____15453 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___235_15452.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____15453;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___235_15452.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____15451
        | uu____15460 -> lopt
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
              ((let uu____15473 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____15473
                then
                  let time_now = FStar_Util.now () in
                  let uu____15475 =
                    let uu____15476 =
                      let uu____15477 =
                        FStar_Util.time_diff time_then time_now in
                      FStar_Pervasives_Native.snd uu____15477 in
                    FStar_Util.string_of_int uu____15476 in
                  let uu____15482 = FStar_Syntax_Print.term_to_string tm in
                  let uu____15483 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                    uu____15475 uu____15482 uu____15483
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___236_15501 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___236_15501.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____15594  ->
                    let uu____15595 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____15595);
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
              let uu____15631 =
                let uu___237_15632 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___237_15632.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___237_15632.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____15631
          | (Arg (Univ uu____15633,uu____15634,uu____15635))::uu____15636 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____15639,uu____15640))::uu____15641 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____15657),aq,r))::stack2 ->
              (log cfg
                 (fun uu____15686  ->
                    let uu____15687 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____15687);
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
                 (let uu____15697 = FStar_ST.op_Bang m in
                  match uu____15697 with
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
                  | FStar_Pervasives_Native.Some (uu____15817,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq)
                          FStar_Pervasives_Native.None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 =
                FStar_Syntax_Syntax.extend_app head1 (t, aq)
                  FStar_Pervasives_Native.None r in
              let uu____15841 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____15841
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____15851  ->
                    let uu____15852 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____15852);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____15857 =
                  log cfg
                    (fun uu____15862  ->
                       let uu____15863 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____15864 =
                         let uu____15865 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____15882  ->
                                   match uu____15882 with
                                   | (p,uu____15892,uu____15893) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____15865
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____15863 uu____15864);
                  (let whnf1 = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___180_15910  ->
                               match uu___180_15910 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____15911 -> false)) in
                     let steps' =
                       let uu____15915 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____15915
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     only_strong_steps
                       (let uu___238_15921 = cfg in
                        {
                          steps = (FStar_List.append steps' cfg.steps);
                          tcenv = (uu___238_15921.tcenv);
                          delta_level = new_delta;
                          primitive_steps = (uu___238_15921.primitive_steps)
                        }) in
                   let norm_or_whnf env2 t1 =
                     if whnf1
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____15965 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____15988 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____16054  ->
                                   fun uu____16055  ->
                                     match (uu____16054, uu____16055) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____16158 = norm_pat env3 p1 in
                                         (match uu____16158 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____15988 with
                          | (pats1,env3) ->
                              ((let uu___239_16260 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.p =
                                    (uu___239_16260.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___240_16279 = x in
                           let uu____16280 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___240_16279.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___240_16279.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16280
                           } in
                         ((let uu___241_16288 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.p =
                               (uu___241_16288.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___242_16293 = x in
                           let uu____16294 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___242_16293.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___242_16293.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16294
                           } in
                         ((let uu___243_16302 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.p =
                               (uu___243_16302.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___244_16312 = x in
                           let uu____16313 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___244_16312.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___244_16312.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16313
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___245_16322 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.p =
                               (uu___245_16322.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf1 -> branches
                     | uu____16326 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____16340 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____16340 with
                                 | (p,wopt,e) ->
                                     let uu____16360 = norm_pat env1 p in
                                     (match uu____16360 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Pervasives_Native.Some w
                                                ->
                                                let uu____16391 =
                                                  norm_or_whnf env2 w in
                                                FStar_Pervasives_Native.Some
                                                  uu____16391 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____16397 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____16397) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____16407) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____16412 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____16413;
                        FStar_Syntax_Syntax.fv_delta = uu____16414;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Data_ctor );_}
                      -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____16415;
                        FStar_Syntax_Syntax.fv_delta = uu____16416;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Record_ctor uu____16417);_}
                      -> true
                  | uu____16424 -> false in
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
                  let uu____16553 =
                    FStar_Syntax_Util.head_and_args scrutinee1 in
                  match uu____16553 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var uu____16602 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_wild uu____16605 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____16608 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee1.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____16627 ->
                                let uu____16628 =
                                  let uu____16629 = is_cons head1 in
                                  Prims.op_Negation uu____16629 in
                                FStar_Util.Inr uu____16628)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____16650 =
                             let uu____16651 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____16651.FStar_Syntax_Syntax.n in
                           (match uu____16650 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____16661 ->
                                let uu____16662 =
                                  let uu____16663 = is_cons head1 in
                                  Prims.op_Negation uu____16663 in
                                FStar_Util.Inr uu____16662))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____16716)::rest_a,(p1,uu____16719)::rest_p) ->
                      let uu____16763 = matches_pat t1 p1 in
                      (match uu____16763 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____16788 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____16890 = matches_pat scrutinee1 p1 in
                      (match uu____16890 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____16910  ->
                                 let uu____16911 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____16912 =
                                   let uu____16913 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____16913
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____16911 uu____16912);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____16930 =
                                        let uu____16931 =
                                          let uu____16950 =
                                            FStar_Util.mk_ref
                                              (FStar_Pervasives_Native.Some
                                                 ([], t1)) in
                                          ([], t1, uu____16950, false) in
                                        Clos uu____16931 in
                                      uu____16930 :: env2) env1 s in
                             let uu____17003 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____17003))) in
                let uu____17004 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____17004
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___181_17027  ->
                match uu___181_17027 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____17031 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____17037 -> d in
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
            let uu___246_17066 = config s e in
            {
              steps = (uu___246_17066.steps);
              tcenv = (uu___246_17066.tcenv);
              delta_level = (uu___246_17066.delta_level);
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
      fun t  -> let uu____17091 = config s e in norm_comp uu____17091 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____17100 = config [] env in norm_universe uu____17100 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let uu____17109 = config [] env in ghost_to_pure_aux uu____17109 [] c
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
        let uu____17123 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____17123 in
      let uu____17124 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____17124
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___247_17126 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___247_17126.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___247_17126.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____17129  ->
                    let uu____17130 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____17130))
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
            ((let uu____17149 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning
                "Normalization failed with error %s\n" uu____17149);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____17162 = config [AllowUnboundUniverses] env in
          norm_comp uu____17162 [] c
        with
        | e ->
            ((let uu____17169 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning
                "Normalization failed with error %s\n" uu____17169);
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
                   let uu____17209 =
                     let uu____17210 =
                       let uu____17217 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____17217) in
                     FStar_Syntax_Syntax.Tm_refine uu____17210 in
                   mk uu____17209 t01.FStar_Syntax_Syntax.pos
               | uu____17222 -> t2)
          | uu____17223 -> t2 in
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
        let uu____17275 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____17275 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____17304 ->
                 let uu____17311 = FStar_Syntax_Util.abs_formals e in
                 (match uu____17311 with
                  | (actuals,uu____17321,uu____17322) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____17336 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____17336 with
                         | (binders,args) ->
                             let uu____17353 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____17353
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
      | uu____17363 ->
          let uu____17364 = FStar_Syntax_Util.head_and_args t in
          (match uu____17364 with
           | (head1,args) ->
               let uu____17401 =
                 let uu____17402 = FStar_Syntax_Subst.compress head1 in
                 uu____17402.FStar_Syntax_Syntax.n in
               (match uu____17401 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____17405,thead) ->
                    let uu____17431 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____17431 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____17473 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___252_17481 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___252_17481.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___252_17481.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___252_17481.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___252_17481.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___252_17481.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___252_17481.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___252_17481.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___252_17481.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___252_17481.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___252_17481.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___252_17481.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___252_17481.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___252_17481.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___252_17481.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___252_17481.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___252_17481.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___252_17481.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___252_17481.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___252_17481.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___252_17481.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___252_17481.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___252_17481.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___252_17481.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___252_17481.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___252_17481.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___252_17481.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___252_17481.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___252_17481.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___252_17481.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___252_17481.FStar_TypeChecker_Env.dsenv)
                                 }) t in
                            match uu____17473 with
                            | (uu____17482,ty,uu____17484) ->
                                eta_expand_with_type env t ty))
                | uu____17485 ->
                    let uu____17486 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___253_17494 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___253_17494.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___253_17494.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___253_17494.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___253_17494.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___253_17494.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___253_17494.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___253_17494.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___253_17494.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___253_17494.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___253_17494.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___253_17494.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___253_17494.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___253_17494.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___253_17494.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___253_17494.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___253_17494.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___253_17494.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___253_17494.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___253_17494.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___253_17494.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___253_17494.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___253_17494.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___253_17494.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___253_17494.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___253_17494.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___253_17494.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___253_17494.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___253_17494.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___253_17494.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___253_17494.FStar_TypeChecker_Env.dsenv)
                         }) t in
                    (match uu____17486 with
                     | (uu____17495,ty,uu____17497) ->
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
            | (uu____17575,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____17581,FStar_Util.Inl t) ->
                let uu____17587 =
                  let uu____17590 =
                    let uu____17591 =
                      let uu____17604 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____17604) in
                    FStar_Syntax_Syntax.Tm_arrow uu____17591 in
                  FStar_Syntax_Syntax.mk uu____17590 in
                uu____17587 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____17608 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____17608 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____17635 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____17690 ->
                    let uu____17691 =
                      let uu____17700 =
                        let uu____17701 = FStar_Syntax_Subst.compress t3 in
                        uu____17701.FStar_Syntax_Syntax.n in
                      (uu____17700, tc) in
                    (match uu____17691 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____17726) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____17763) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____17802,FStar_Util.Inl uu____17803) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____17826 -> failwith "Impossible") in
              (match uu____17635 with
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
          let uu____17935 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____17935 with
          | (univ_names1,binders1,tc) ->
              let uu____17993 = FStar_Util.left tc in
              (univ_names1, binders1, uu____17993)
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
          let uu____18032 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____18032 with
          | (univ_names1,binders1,tc) ->
              let uu____18092 = FStar_Util.right tc in
              (univ_names1, binders1, uu____18092)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____18127 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____18127 with
           | (univ_names1,binders1,typ1) ->
               let uu___254_18155 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___254_18155.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___254_18155.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___254_18155.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___254_18155.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___255_18176 = s in
          let uu____18177 =
            let uu____18178 =
              let uu____18187 = FStar_List.map (elim_uvars env) sigs in
              (uu____18187, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____18178 in
          {
            FStar_Syntax_Syntax.sigel = uu____18177;
            FStar_Syntax_Syntax.sigrng =
              (uu___255_18176.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___255_18176.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___255_18176.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___255_18176.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____18204 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____18204 with
           | (univ_names1,uu____18222,typ1) ->
               let uu___256_18236 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___256_18236.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___256_18236.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___256_18236.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___256_18236.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____18242 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____18242 with
           | (univ_names1,uu____18260,typ1) ->
               let uu___257_18274 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___257_18274.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___257_18274.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___257_18274.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___257_18274.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____18308 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____18308 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____18331 =
                            let uu____18332 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____18332 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____18331 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___258_18335 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___258_18335.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___258_18335.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___259_18336 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___259_18336.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___259_18336.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___259_18336.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___259_18336.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___260_18348 = s in
          let uu____18349 =
            let uu____18350 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____18350 in
          {
            FStar_Syntax_Syntax.sigel = uu____18349;
            FStar_Syntax_Syntax.sigrng =
              (uu___260_18348.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___260_18348.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___260_18348.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___260_18348.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____18354 = elim_uvars_aux_t env us [] t in
          (match uu____18354 with
           | (us1,uu____18372,t1) ->
               let uu___261_18386 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___261_18386.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___261_18386.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___261_18386.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___261_18386.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____18387 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____18389 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____18389 with
           | (univs1,binders,signature) ->
               let uu____18417 =
                 let uu____18426 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____18426 with
                 | (univs_opening,univs2) ->
                     let uu____18453 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____18453) in
               (match uu____18417 with
                | (univs_opening,univs_closing) ->
                    let uu____18470 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____18476 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____18477 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____18476, uu____18477) in
                    (match uu____18470 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____18499 =
                           match uu____18499 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____18517 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____18517 with
                                | (us1,t1) ->
                                    let uu____18528 =
                                      let uu____18533 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____18540 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____18533, uu____18540) in
                                    (match uu____18528 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____18553 =
                                           let uu____18558 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____18567 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____18558, uu____18567) in
                                         (match uu____18553 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____18583 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____18583 in
                                              let uu____18584 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____18584 with
                                               | (uu____18605,uu____18606,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____18621 =
                                                       let uu____18622 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____18622 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____18621 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____18627 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____18627 with
                           | (uu____18640,uu____18641,t1) -> t1 in
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
                             | uu____18701 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____18718 =
                               let uu____18719 =
                                 FStar_Syntax_Subst.compress body in
                               uu____18719.FStar_Syntax_Syntax.n in
                             match uu____18718 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____18778 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____18807 =
                               let uu____18808 =
                                 FStar_Syntax_Subst.compress t in
                               uu____18808.FStar_Syntax_Syntax.n in
                             match uu____18807 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____18829) ->
                                 let uu____18850 = destruct_action_body body in
                                 (match uu____18850 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____18895 ->
                                 let uu____18896 = destruct_action_body t in
                                 (match uu____18896 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____18945 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____18945 with
                           | (action_univs,t) ->
                               let uu____18954 = destruct_action_typ_templ t in
                               (match uu____18954 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___262_18995 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___262_18995.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___262_18995.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___263_18997 = ed in
                           let uu____18998 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____18999 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____19000 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____19001 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____19002 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____19003 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____19004 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____19005 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____19006 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____19007 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____19008 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____19009 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____19010 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____19011 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___263_18997.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___263_18997.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____18998;
                             FStar_Syntax_Syntax.bind_wp = uu____18999;
                             FStar_Syntax_Syntax.if_then_else = uu____19000;
                             FStar_Syntax_Syntax.ite_wp = uu____19001;
                             FStar_Syntax_Syntax.stronger = uu____19002;
                             FStar_Syntax_Syntax.close_wp = uu____19003;
                             FStar_Syntax_Syntax.assert_p = uu____19004;
                             FStar_Syntax_Syntax.assume_p = uu____19005;
                             FStar_Syntax_Syntax.null_wp = uu____19006;
                             FStar_Syntax_Syntax.trivial = uu____19007;
                             FStar_Syntax_Syntax.repr = uu____19008;
                             FStar_Syntax_Syntax.return_repr = uu____19009;
                             FStar_Syntax_Syntax.bind_repr = uu____19010;
                             FStar_Syntax_Syntax.actions = uu____19011
                           } in
                         let uu___264_19014 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___264_19014.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___264_19014.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___264_19014.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___264_19014.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___182_19031 =
            match uu___182_19031 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____19058 = elim_uvars_aux_t env us [] t in
                (match uu____19058 with
                 | (us1,uu____19082,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___265_19101 = sub_eff in
            let uu____19102 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____19105 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___265_19101.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___265_19101.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____19102;
              FStar_Syntax_Syntax.lift = uu____19105
            } in
          let uu___266_19108 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___266_19108.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___266_19108.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___266_19108.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___266_19108.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____19118 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____19118 with
           | (univ_names1,binders1,comp1) ->
               let uu___267_19152 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___267_19152.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___267_19152.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___267_19152.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___267_19152.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____19163 -> s