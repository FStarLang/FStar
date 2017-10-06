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
  fun uu___150_395  ->
    match uu___150_395 with
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
    let uu___166_513 = cfg in
    let uu____514 = only_strong_steps' cfg.primitive_steps in
    {
      steps = (uu___166_513.steps);
      tcenv = (uu___166_513.tcenv);
      delta_level = (uu___166_513.delta_level);
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
  fun uu___151_1760  ->
    match uu___151_1760 with
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
  fun uu___152_1867  ->
    match uu___152_1867 with | [] -> true | uu____1870 -> false
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
                           (let uu___171_3044 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___171_3044.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___171_3044.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____3038)) in
                  (match uu____3008 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___172_3060 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___172_3060.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___172_3060.FStar_Syntax_Syntax.lbeff);
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
                           (let uu___173_3143 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___173_3143.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___173_3143.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_43  -> FStar_Util.Inl _0_43)) in
                    let uu___174_3144 = lb in
                    let uu____3145 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___174_3144.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___174_3144.FStar_Syntax_Syntax.lbeff);
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
                                   ((let uu___175_3602 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___175_3602.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___176_3621 = x in
                                let uu____3622 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___176_3621.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___176_3621.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3622
                                } in
                              ((let uu___177_3630 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___177_3630.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___178_3635 = x in
                                let uu____3636 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___178_3635.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___178_3635.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3636
                                } in
                              ((let uu___179_3644 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___179_3644.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___180_3654 = x in
                                let uu____3655 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___180_3654.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___180_3654.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3655
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___181_3664 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___181_3664.FStar_Syntax_Syntax.p)
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
                          let uu___182_4030 = b in
                          let uu____4031 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___182_4030.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___182_4030.FStar_Syntax_Syntax.index);
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
                        (fun uu___153_4168  ->
                           match uu___153_4168 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____4172 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____4172
                           | f -> f)) in
                 let uu____4176 =
                   let uu___183_4177 = c1 in
                   let uu____4178 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____4178;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___183_4177.FStar_Syntax_Syntax.effect_name);
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
         (fun uu___154_4188  ->
            match uu___154_4188 with
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
                   (fun uu___155_4212  ->
                      match uu___155_4212 with
                      | FStar_Syntax_Syntax.DECREASES uu____4213 -> false
                      | uu____4216 -> true)) in
            let rc1 =
              let uu___184_4218 = rc in
              let uu____4219 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___184_4218.FStar_Syntax_Syntax.residual_effect);
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
          (let uu___185_5315 = t in
           {
             FStar_Syntax_Syntax.n = (uu___185_5315.FStar_Syntax_Syntax.n);
             FStar_Syntax_Syntax.pos = r2;
             FStar_Syntax_Syntax.vars =
               (uu___185_5315.FStar_Syntax_Syntax.vars)
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
               (let uu___186_7137 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___186_7137.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___186_7137.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___187_7141 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___187_7141.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___187_7141.FStar_Syntax_Syntax.vars)
                })
         | uu____7142 -> FStar_Pervasives_Native.None)
    | (_typ,uu____7144)::uu____7145::(a1,uu____7147)::(a2,uu____7149)::[] ->
        let uu____7198 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____7198 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___186_7204 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___186_7204.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___186_7204.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___187_7208 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___187_7208.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___187_7208.FStar_Syntax_Syntax.vars)
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
        (let uu___188_7327 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___188_7327.tcenv);
           delta_level = (uu___188_7327.delta_level);
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
           let uu___189_7349 = t in
           {
             FStar_Syntax_Syntax.n = (uu___189_7349.FStar_Syntax_Syntax.n);
             FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
             FStar_Syntax_Syntax.vars =
               (uu___189_7349.FStar_Syntax_Syntax.vars)
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
  fun uu___156_10424  ->
    match uu___156_10424 with
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
  fun uu___157_10617  ->
    match uu___157_10617 with
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
                 let uu___190_10936 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___190_10936.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___190_10936.FStar_Syntax_Syntax.vars)
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
                 let uu___191_10977 = cfg in
                 let uu____10978 =
                   FStar_List.filter
                     (fun uu___158_10981  ->
                        match uu___158_10981 with
                        | UnfoldOnly uu____10982 -> false
                        | NoDeltaSteps  -> false
                        | uu____10985 -> true) cfg.steps in
                 {
                   steps = uu____10978;
                   tcenv = (uu___191_10977.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___191_10977.primitive_steps)
                 } in
               let uu____10986 = get_norm_request (norm cfg' env []) args in
               (match uu____10986 with
                | (s,tm) ->
                    let delta_level =
                      let uu____11002 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___159_11007  ->
                                match uu___159_11007 with
                                | UnfoldUntil uu____11008 -> true
                                | UnfoldOnly uu____11009 -> true
                                | uu____11012 -> false)) in
                      if uu____11002
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___192_11017 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___192_11017.tcenv);
                        delta_level;
                        primitive_steps = (uu___192_11017.primitive_steps)
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
                      (fun uu___160_11357  ->
                         match uu___160_11357 with
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
                           (fun uu___161_11369  ->
                              match uu___161_11369 with
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
                            norm cfg env2 stack1 t')
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____11640)::uu____11641 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11650)::uu____11651 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11661,uu____11662))::stack_rest ->
                    (match c with
                     | Univ uu____11666 -> norm cfg (c :: env) stack_rest t1
                     | uu____11667 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____11672::[] ->
                              (log cfg
                                 (fun uu____11688  ->
                                    let uu____11689 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11689);
                               norm cfg (c :: env) stack_rest body)
                          | uu____11690::tl1 ->
                              (log cfg
                                 (fun uu____11709  ->
                                    let uu____11710 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11710);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___193_11740 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___193_11740.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____11825  ->
                          let uu____11826 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11826);
                     norm cfg env stack2 t1)
                | (Debug uu____11827)::uu____11828 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11835 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11835
                    else
                      (let uu____11837 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11837 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11861  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11877 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11877
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11887 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11887)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___194_11892 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___194_11892.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___194_11892.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11893 -> lopt in
                           (log cfg
                              (fun uu____11899  ->
                                 let uu____11900 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11900);
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
                | (Meta uu____11917)::uu____11918 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11925 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11925
                    else
                      (let uu____11927 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11927 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11951  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11967 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11967
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11977 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11977)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___194_11982 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___194_11982.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___194_11982.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11983 -> lopt in
                           (log cfg
                              (fun uu____11989  ->
                                 let uu____11990 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11990);
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
                | (Let uu____12007)::uu____12008 ->
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
                                   (let uu___194_12076 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___194_12076.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___194_12076.FStar_Syntax_Syntax.residual_flags)
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
                             let cfg1 = only_strong_steps cfg in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____12101)::uu____12102 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12111 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12111
                    else
                      (let uu____12113 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12113 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12137  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12153 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12153
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12163 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12163)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___194_12168 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___194_12168.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___194_12168.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12169 -> lopt in
                           (log cfg
                              (fun uu____12175  ->
                                 let uu____12176 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12176);
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
                | (Abs uu____12193)::uu____12194 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12209 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12209
                    else
                      (let uu____12211 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12211 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12235  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12251 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12251
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12261 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12261)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___194_12266 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___194_12266.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___194_12266.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12267 -> lopt in
                           (log cfg
                              (fun uu____12273  ->
                                 let uu____12274 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12274);
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
                                   (let uu___194_12348 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___194_12348.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___194_12348.FStar_Syntax_Syntax.residual_flags)
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
                      (fun uu____12411  ->
                         fun stack2  ->
                           match uu____12411 with
                           | (a,aq) ->
                               let uu____12423 =
                                 let uu____12424 =
                                   let uu____12431 =
                                     let uu____12432 =
                                       let uu____12451 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____12451, false) in
                                     Clos uu____12432 in
                                   (uu____12431, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____12424 in
                               uu____12423 :: stack2) args) in
               (log cfg
                  (fun uu____12503  ->
                     let uu____12504 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12504);
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
                             ((let uu___195_12528 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___195_12528.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___195_12528.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____12529 ->
                      let uu____12534 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12534)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____12537 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____12537 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____12562 =
                          let uu____12563 =
                            let uu____12570 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___196_12572 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___196_12572.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___196_12572.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12570) in
                          FStar_Syntax_Syntax.Tm_refine uu____12563 in
                        mk uu____12562 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____12591 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____12591
               else
                 (let uu____12593 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____12593 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12601 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12613  -> Dummy :: env1) env) in
                        norm_comp cfg uu____12601 c1 in
                      let t2 =
                        let uu____12623 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____12623 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____12682)::uu____12683 -> norm cfg env stack1 t11
                | (Arg uu____12692)::uu____12693 -> norm cfg env stack1 t11
                | (App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____12702;
                       FStar_Syntax_Syntax.vars = uu____12703;_},uu____12704,uu____12705))::uu____12706
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____12713)::uu____12714 ->
                    norm cfg env stack1 t11
                | uu____12723 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____12727  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____12744 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____12744
                        | FStar_Util.Inr c ->
                            let uu____12752 = norm_comp cfg env c in
                            FStar_Util.Inr uu____12752 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____12758 =
                        let uu____12759 =
                          let uu____12760 =
                            let uu____12787 = FStar_Syntax_Util.unascribe t12 in
                            (uu____12787, (tc1, tacopt1), l) in
                          FStar_Syntax_Syntax.Tm_ascribed uu____12760 in
                        mk uu____12759 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____12758)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____12863,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____12864;
                               FStar_Syntax_Syntax.lbunivs = uu____12865;
                               FStar_Syntax_Syntax.lbtyp = uu____12866;
                               FStar_Syntax_Syntax.lbeff = uu____12867;
                               FStar_Syntax_Syntax.lbdef = uu____12868;_}::uu____12869),uu____12870)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____12906 =
                 (let uu____12909 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____12909) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____12911 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____12911))) in
               if uu____12906
               then
                 let env1 =
                   let uu____12915 =
                     let uu____12916 =
                       let uu____12935 =
                         FStar_Util.mk_ref FStar_Pervasives_Native.None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____12935,
                         false) in
                     Clos uu____12916 in
                   uu____12915 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____12987 =
                    let uu____12992 =
                      let uu____12993 =
                        let uu____12994 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____12994
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____12993] in
                    FStar_Syntax_Subst.open_term uu____12992 body in
                  match uu____12987 with
                  | (bs,body1) ->
                      let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                      let lbname =
                        let x =
                          let uu____13008 = FStar_List.hd bs in
                          FStar_Pervasives_Native.fst uu____13008 in
                        FStar_Util.Inl
                          (let uu___197_13018 = x in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___197_13018.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___197_13018.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = ty
                           }) in
                      let lb1 =
                        let uu___198_13020 = lb in
                        let uu____13021 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = lbname;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___198_13020.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = ty;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___198_13020.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____13021
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____13038  -> Dummy :: env1)
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
               let uu____13062 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____13062 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____13098 =
                               let uu___199_13099 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___199_13099.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___199_13099.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____13098 in
                           let uu____13100 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____13100 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____13120 =
                                   FStar_List.map (fun uu____13124  -> Dummy)
                                     lbs1 in
                                 let uu____13125 =
                                   let uu____13128 =
                                     FStar_List.map
                                       (fun uu____13136  -> Dummy) xs1 in
                                   FStar_List.append uu____13128 env in
                                 FStar_List.append uu____13120 uu____13125 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13148 =
                                       let uu___200_13149 = rc in
                                       let uu____13150 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___200_13149.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13150;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___200_13149.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____13148
                                 | uu____13157 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___201_13161 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___201_13161.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___201_13161.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____13165 =
                        FStar_List.map (fun uu____13169  -> Dummy) lbs2 in
                      FStar_List.append uu____13165 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____13171 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____13171 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___202_13187 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___202_13187.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___202_13187.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____13214 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____13214
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13233 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13284  ->
                        match uu____13284 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____13357 =
                                let uu___203_13358 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___203_13358.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___203_13358.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____13357 in
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
               (match uu____13233 with
                | (rec_env,memos,uu____13486) ->
                    let uu____13515 =
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
                             let uu____13980 =
                               let uu____13981 =
                                 let uu____14000 =
                                   FStar_Util.mk_ref
                                     FStar_Pervasives_Native.None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____14000, false) in
                               Clos uu____13981 in
                             uu____13980 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
                    norm cfg body_env stack1 body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (match m with
                | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                    let uu____14067 =
                      let uu____14068 = should_reify cfg stack1 in
                      Prims.op_Negation uu____14068 in
                    if uu____14067
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____14078 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____14078
                        then
                          let uu___204_14079 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___204_14079.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps =
                              (uu___204_14079.primitive_steps)
                          }
                        else
                          (let uu___205_14081 = cfg in
                           {
                             steps =
                               (FStar_List.append [Exclude Zeta] cfg.steps);
                             tcenv = (uu___205_14081.tcenv);
                             delta_level = (uu___205_14081.delta_level);
                             primitive_steps =
                               (uu___205_14081.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____14083 =
                         let uu____14084 = FStar_Syntax_Subst.compress head1 in
                         uu____14084.FStar_Syntax_Syntax.n in
                       match uu____14083 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____14102 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____14102 with
                            | (uu____14103,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____14109 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____14117 =
                                         let uu____14118 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____14118.FStar_Syntax_Syntax.n in
                                       match uu____14117 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____14124,uu____14125))
                                           ->
                                           let uu____14134 =
                                             let uu____14135 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____14135.FStar_Syntax_Syntax.n in
                                           (match uu____14134 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____14141,msrc,uu____14143))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____14152 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14152
                                            | uu____14153 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____14154 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____14155 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____14155 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___206_14160 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___206_14160.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___206_14160.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___206_14160.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____14161 =
                                            FStar_List.tl stack1 in
                                          let uu____14162 =
                                            let uu____14163 =
                                              let uu____14166 =
                                                let uu____14167 =
                                                  let uu____14180 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____14180) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____14167 in
                                              FStar_Syntax_Syntax.mk
                                                uu____14166 in
                                            uu____14163
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____14161
                                            uu____14162
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____14196 =
                                            let uu____14197 = is_return body in
                                            match uu____14197 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____14201;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____14202;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____14207 -> false in
                                          if uu____14196
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
                                               let uu____14231 =
                                                 let uu____14234 =
                                                   let uu____14235 =
                                                     let uu____14252 =
                                                       let uu____14255 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____14255] in
                                                     (uu____14252, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc)) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____14235 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____14234 in
                                               uu____14231
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____14271 =
                                                 let uu____14272 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____14272.FStar_Syntax_Syntax.n in
                                               match uu____14271 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____14278::uu____14279::[])
                                                   ->
                                                   let uu____14286 =
                                                     let uu____14289 =
                                                       let uu____14290 =
                                                         let uu____14297 =
                                                           let uu____14300 =
                                                             let uu____14301
                                                               =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____14301 in
                                                           let uu____14302 =
                                                             let uu____14305
                                                               =
                                                               let uu____14306
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____14306 in
                                                             [uu____14305] in
                                                           uu____14300 ::
                                                             uu____14302 in
                                                         (bind1, uu____14297) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____14290 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____14289 in
                                                   uu____14286
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____14314 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____14320 =
                                                 let uu____14323 =
                                                   let uu____14324 =
                                                     let uu____14339 =
                                                       let uu____14342 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____14343 =
                                                         let uu____14346 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____14347 =
                                                           let uu____14350 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____14351 =
                                                             let uu____14354
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____14355
                                                               =
                                                               let uu____14358
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____14359
                                                                 =
                                                                 let uu____14362
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____14362] in
                                                               uu____14358 ::
                                                                 uu____14359 in
                                                             uu____14354 ::
                                                               uu____14355 in
                                                           uu____14350 ::
                                                             uu____14351 in
                                                         uu____14346 ::
                                                           uu____14347 in
                                                       uu____14342 ::
                                                         uu____14343 in
                                                     (bind_inst, uu____14339) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____14324 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____14323 in
                                               uu____14320
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____14370 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____14370 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____14394 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____14394 with
                            | (uu____14395,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____14430 =
                                        let uu____14431 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____14431.FStar_Syntax_Syntax.n in
                                      match uu____14430 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____14437) -> t4
                                      | uu____14442 -> head2 in
                                    let uu____14443 =
                                      let uu____14444 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____14444.FStar_Syntax_Syntax.n in
                                    match uu____14443 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____14450 ->
                                        FStar_Pervasives_Native.None in
                                  let uu____14451 = maybe_extract_fv head2 in
                                  match uu____14451 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____14461 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____14461
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____14466 =
                                          maybe_extract_fv head3 in
                                        match uu____14466 with
                                        | FStar_Pervasives_Native.Some
                                            uu____14471 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____14472 ->
                                            FStar_Pervasives_Native.Some
                                              false in
                                      (head3, action_unfolded)
                                  | uu____14477 ->
                                      (head2, FStar_Pervasives_Native.None) in
                                ((let is_arg_impure uu____14492 =
                                    match uu____14492 with
                                    | (e,q) ->
                                        let uu____14499 =
                                          let uu____14500 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____14500.FStar_Syntax_Syntax.n in
                                        (match uu____14499 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____14515 -> false) in
                                  let uu____14516 =
                                    let uu____14517 =
                                      let uu____14524 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____14524 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____14517 in
                                  if uu____14516
                                  then
                                    let uu____14529 =
                                      let uu____14530 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____14530 in
                                    failwith uu____14529
                                  else ());
                                 (let uu____14532 =
                                    maybe_unfold_action head_app in
                                  match uu____14532 with
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
                                      let uu____14571 = FStar_List.tl stack1 in
                                      norm cfg env uu____14571 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____14585 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____14585 in
                           let uu____14586 = FStar_List.tl stack1 in
                           norm cfg env uu____14586 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____14707  ->
                                     match uu____14707 with
                                     | (pat,wopt,tm) ->
                                         let uu____14755 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____14755))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____14787 = FStar_List.tl stack1 in
                           norm cfg env uu____14787 tm
                       | uu____14788 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let uu____14796 = should_reify cfg stack1 in
                    if uu____14796
                    then
                      let uu____14797 = FStar_List.tl stack1 in
                      let uu____14798 =
                        let uu____14799 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____14799 in
                      norm cfg env uu____14797 uu____14798
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____14802 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____14802
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___207_14811 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___207_14811.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___207_14811.primitive_steps)
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
                | uu____14813 ->
                    if FStar_List.contains Unmeta cfg.steps
                    then norm cfg env stack1 head1
                    else
                      (match stack1 with
                       | uu____14815::uu____14816 ->
                           (match m with
                            | FStar_Syntax_Syntax.Meta_labeled
                                (l,r,uu____14821) ->
                                norm cfg env ((Meta (m, r)) :: stack1) head1
                            | FStar_Syntax_Syntax.Meta_alien uu____14822 ->
                                rebuild cfg env stack1 t1
                            | FStar_Syntax_Syntax.Meta_pattern args ->
                                let args1 = norm_pattern_args cfg env args in
                                norm cfg env
                                  ((Meta
                                      ((FStar_Syntax_Syntax.Meta_pattern
                                          args1),
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) head1
                            | uu____14853 -> norm cfg env stack1 head1)
                       | [] ->
                           let head2 = norm cfg env [] head1 in
                           let m1 =
                             match m with
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let uu____14867 =
                                   norm_pattern_args cfg env args in
                                 FStar_Syntax_Syntax.Meta_pattern uu____14867
                             | uu____14878 -> m in
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
              let uu____14890 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____14890 with
              | (uu____14891,return_repr) ->
                  let return_inst =
                    let uu____14900 =
                      let uu____14901 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____14901.FStar_Syntax_Syntax.n in
                    match uu____14900 with
                    | FStar_Syntax_Syntax.Tm_uinst
                        (return_tm,uu____14907::[]) ->
                        let uu____14914 =
                          let uu____14917 =
                            let uu____14918 =
                              let uu____14925 =
                                let uu____14928 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____14928] in
                              (return_tm, uu____14925) in
                            FStar_Syntax_Syntax.Tm_uinst uu____14918 in
                          FStar_Syntax_Syntax.mk uu____14917 in
                        uu____14914 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____14936 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____14939 =
                    let uu____14942 =
                      let uu____14943 =
                        let uu____14958 =
                          let uu____14961 = FStar_Syntax_Syntax.as_arg t in
                          let uu____14962 =
                            let uu____14965 = FStar_Syntax_Syntax.as_arg e in
                            [uu____14965] in
                          uu____14961 :: uu____14962 in
                        (return_inst, uu____14958) in
                      FStar_Syntax_Syntax.Tm_app uu____14943 in
                    FStar_Syntax_Syntax.mk uu____14942 in
                  uu____14939 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____14974 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____14974 with
               | FStar_Pervasives_Native.None  ->
                   let uu____14977 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____14977
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____14978;
                     FStar_TypeChecker_Env.mtarget = uu____14979;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____14980;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____14991;
                     FStar_TypeChecker_Env.mtarget = uu____14992;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____14993;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____15011 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____15011)
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
                (fun uu____15067  ->
                   match uu____15067 with
                   | (a,imp) ->
                       let uu____15078 = norm cfg env [] a in
                       (uu____15078, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___208_15095 = comp1 in
            let uu____15098 =
              let uu____15099 =
                let uu____15108 = norm cfg env [] t in
                let uu____15109 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____15108, uu____15109) in
              FStar_Syntax_Syntax.Total uu____15099 in
            {
              FStar_Syntax_Syntax.n = uu____15098;
              FStar_Syntax_Syntax.pos =
                (uu___208_15095.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___208_15095.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___209_15124 = comp1 in
            let uu____15127 =
              let uu____15128 =
                let uu____15137 = norm cfg env [] t in
                let uu____15138 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____15137, uu____15138) in
              FStar_Syntax_Syntax.GTotal uu____15128 in
            {
              FStar_Syntax_Syntax.n = uu____15127;
              FStar_Syntax_Syntax.pos =
                (uu___209_15124.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___209_15124.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____15190  ->
                      match uu____15190 with
                      | (a,i) ->
                          let uu____15201 = norm cfg env [] a in
                          (uu____15201, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___162_15212  ->
                      match uu___162_15212 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____15216 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____15216
                      | f -> f)) in
            let uu___210_15220 = comp1 in
            let uu____15223 =
              let uu____15224 =
                let uu___211_15225 = ct in
                let uu____15226 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____15227 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____15230 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____15226;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___211_15225.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____15227;
                  FStar_Syntax_Syntax.effect_args = uu____15230;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____15224 in
            {
              FStar_Syntax_Syntax.n = uu____15223;
              FStar_Syntax_Syntax.pos =
                (uu___210_15220.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___210_15220.FStar_Syntax_Syntax.vars)
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
            (let uu___212_15248 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___212_15248.tcenv);
               delta_level = (uu___212_15248.delta_level);
               primitive_steps = (uu___212_15248.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____15253 = norm1 t in
          FStar_Syntax_Util.non_informative uu____15253 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____15256 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___213_15275 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.pos =
                (uu___213_15275.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___213_15275.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____15282 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____15282
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
                    let uu___214_15293 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___214_15293.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___214_15293.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___214_15293.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___215_15295 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___215_15295.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___215_15295.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___215_15295.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___215_15295.FStar_Syntax_Syntax.flags)
                    } in
              let uu___216_15296 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos =
                  (uu___216_15296.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___216_15296.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____15298 -> c
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____15301  ->
        match uu____15301 with
        | (x,imp) ->
            let uu____15304 =
              let uu___217_15305 = x in
              let uu____15306 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___217_15305.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___217_15305.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____15306
              } in
            (uu____15304, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____15312 =
          FStar_List.fold_left
            (fun uu____15330  ->
               fun b  ->
                 match uu____15330 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____15312 with | (nbs,uu____15358) -> FStar_List.rev nbs
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
            let uu____15374 =
              let uu___218_15375 = rc in
              let uu____15376 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___218_15375.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____15376;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___218_15375.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____15374
        | uu____15383 -> lopt
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
              ((let uu____15396 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____15396
                then
                  let time_now = FStar_Util.now () in
                  let uu____15398 =
                    let uu____15399 =
                      let uu____15400 =
                        FStar_Util.time_diff time_then time_now in
                      FStar_Pervasives_Native.snd uu____15400 in
                    FStar_Util.string_of_int uu____15399 in
                  let uu____15405 = FStar_Syntax_Print.term_to_string tm in
                  let uu____15406 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                    uu____15398 uu____15405 uu____15406
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___219_15424 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___219_15424.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____15517  ->
                    let uu____15518 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____15518);
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
              let uu____15554 =
                let uu___220_15555 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___220_15555.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___220_15555.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____15554
          | (Arg (Univ uu____15556,uu____15557,uu____15558))::uu____15559 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____15562,uu____15563))::uu____15564 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____15580),aq,r))::stack2 ->
              (log cfg
                 (fun uu____15609  ->
                    let uu____15610 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____15610);
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
                 (let uu____15620 = FStar_ST.op_Bang m in
                  match uu____15620 with
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
                  | FStar_Pervasives_Native.Some (uu____15740,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq)
                          FStar_Pervasives_Native.None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 =
                FStar_Syntax_Syntax.extend_app head1 (t, aq)
                  FStar_Pervasives_Native.None r in
              let uu____15764 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____15764
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____15774  ->
                    let uu____15775 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____15775);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____15780 =
                  log cfg
                    (fun uu____15785  ->
                       let uu____15786 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____15787 =
                         let uu____15788 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____15805  ->
                                   match uu____15805 with
                                   | (p,uu____15815,uu____15816) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____15788
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____15786 uu____15787);
                  (let whnf1 = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___163_15833  ->
                               match uu___163_15833 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____15834 -> false)) in
                     let steps' =
                       let uu____15838 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____15838
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     only_strong_steps
                       (let uu___221_15844 = cfg in
                        {
                          steps = (FStar_List.append steps' cfg.steps);
                          tcenv = (uu___221_15844.tcenv);
                          delta_level = new_delta;
                          primitive_steps = (uu___221_15844.primitive_steps)
                        }) in
                   let norm_or_whnf env2 t1 =
                     if whnf1
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____15888 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____15911 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____15977  ->
                                   fun uu____15978  ->
                                     match (uu____15977, uu____15978) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____16081 = norm_pat env3 p1 in
                                         (match uu____16081 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____15911 with
                          | (pats1,env3) ->
                              ((let uu___222_16183 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.p =
                                    (uu___222_16183.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___223_16202 = x in
                           let uu____16203 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___223_16202.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___223_16202.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16203
                           } in
                         ((let uu___224_16211 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.p =
                               (uu___224_16211.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___225_16216 = x in
                           let uu____16217 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___225_16216.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___225_16216.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16217
                           } in
                         ((let uu___226_16225 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.p =
                               (uu___226_16225.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___227_16235 = x in
                           let uu____16236 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___227_16235.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___227_16235.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16236
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___228_16245 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.p =
                               (uu___228_16245.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf1 -> branches
                     | uu____16249 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____16263 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____16263 with
                                 | (p,wopt,e) ->
                                     let uu____16283 = norm_pat env1 p in
                                     (match uu____16283 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Pervasives_Native.Some w
                                                ->
                                                let uu____16314 =
                                                  norm_or_whnf env2 w in
                                                FStar_Pervasives_Native.Some
                                                  uu____16314 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____16320 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____16320) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____16330) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____16335 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____16336;
                        FStar_Syntax_Syntax.fv_delta = uu____16337;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Data_ctor );_}
                      -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____16338;
                        FStar_Syntax_Syntax.fv_delta = uu____16339;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Record_ctor uu____16340);_}
                      -> true
                  | uu____16347 -> false in
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
                  let uu____16476 =
                    FStar_Syntax_Util.head_and_args scrutinee1 in
                  match uu____16476 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var uu____16525 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_wild uu____16528 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____16531 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee1.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____16550 ->
                                let uu____16551 =
                                  let uu____16552 = is_cons head1 in
                                  Prims.op_Negation uu____16552 in
                                FStar_Util.Inr uu____16551)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____16573 =
                             let uu____16574 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____16574.FStar_Syntax_Syntax.n in
                           (match uu____16573 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____16584 ->
                                let uu____16585 =
                                  let uu____16586 = is_cons head1 in
                                  Prims.op_Negation uu____16586 in
                                FStar_Util.Inr uu____16585))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____16639)::rest_a,(p1,uu____16642)::rest_p) ->
                      let uu____16686 = matches_pat t1 p1 in
                      (match uu____16686 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____16711 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____16813 = matches_pat scrutinee1 p1 in
                      (match uu____16813 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____16833  ->
                                 let uu____16834 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____16835 =
                                   let uu____16836 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____16836
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____16834 uu____16835);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____16853 =
                                        let uu____16854 =
                                          let uu____16873 =
                                            FStar_Util.mk_ref
                                              (FStar_Pervasives_Native.Some
                                                 ([], t1)) in
                                          ([], t1, uu____16873, false) in
                                        Clos uu____16854 in
                                      uu____16853 :: env2) env1 s in
                             let uu____16926 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____16926))) in
                let uu____16927 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____16927
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___164_16950  ->
                match uu___164_16950 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____16954 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____16960 -> d in
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
            let uu___229_16989 = config s e in
            {
              steps = (uu___229_16989.steps);
              tcenv = (uu___229_16989.tcenv);
              delta_level = (uu___229_16989.delta_level);
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
      fun t  -> let uu____17014 = config s e in norm_comp uu____17014 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____17023 = config [] env in norm_universe uu____17023 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let uu____17032 = config [] env in ghost_to_pure_aux uu____17032 [] c
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
        let uu____17046 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____17046 in
      let uu____17047 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____17047
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___230_17049 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___230_17049.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___230_17049.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____17052  ->
                    let uu____17053 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____17053))
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
            ((let uu____17072 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____17072);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____17085 = config [AllowUnboundUniverses] env in
          norm_comp uu____17085 [] c
        with
        | e ->
            ((let uu____17092 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____17092);
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
                   let uu____17132 =
                     let uu____17133 =
                       let uu____17140 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____17140) in
                     FStar_Syntax_Syntax.Tm_refine uu____17133 in
                   mk uu____17132 t01.FStar_Syntax_Syntax.pos
               | uu____17145 -> t2)
          | uu____17146 -> t2 in
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
        let uu____17198 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____17198 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____17227 ->
                 let uu____17234 = FStar_Syntax_Util.abs_formals e in
                 (match uu____17234 with
                  | (actuals,uu____17244,uu____17245) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____17259 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____17259 with
                         | (binders,args) ->
                             let uu____17276 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____17276
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
      | uu____17286 ->
          let uu____17287 = FStar_Syntax_Util.head_and_args t in
          (match uu____17287 with
           | (head1,args) ->
               let uu____17324 =
                 let uu____17325 = FStar_Syntax_Subst.compress head1 in
                 uu____17325.FStar_Syntax_Syntax.n in
               (match uu____17324 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____17328,thead) ->
                    let uu____17354 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____17354 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____17396 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___235_17404 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___235_17404.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___235_17404.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___235_17404.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___235_17404.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___235_17404.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___235_17404.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___235_17404.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___235_17404.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___235_17404.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___235_17404.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___235_17404.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___235_17404.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___235_17404.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___235_17404.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___235_17404.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___235_17404.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___235_17404.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___235_17404.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___235_17404.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___235_17404.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___235_17404.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___235_17404.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___235_17404.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___235_17404.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___235_17404.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___235_17404.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___235_17404.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___235_17404.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___235_17404.FStar_TypeChecker_Env.tc_hooks)
                                 }) t in
                            match uu____17396 with
                            | (uu____17405,ty,uu____17407) ->
                                eta_expand_with_type env t ty))
                | uu____17408 ->
                    let uu____17409 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___236_17417 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___236_17417.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___236_17417.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___236_17417.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___236_17417.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___236_17417.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___236_17417.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___236_17417.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___236_17417.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___236_17417.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___236_17417.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___236_17417.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___236_17417.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___236_17417.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___236_17417.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___236_17417.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___236_17417.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___236_17417.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___236_17417.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___236_17417.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___236_17417.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___236_17417.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___236_17417.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___236_17417.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___236_17417.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___236_17417.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___236_17417.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___236_17417.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___236_17417.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___236_17417.FStar_TypeChecker_Env.tc_hooks)
                         }) t in
                    (match uu____17409 with
                     | (uu____17418,ty,uu____17420) ->
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
            | (uu____17498,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____17504,FStar_Util.Inl t) ->
                let uu____17510 =
                  let uu____17513 =
                    let uu____17514 =
                      let uu____17527 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____17527) in
                    FStar_Syntax_Syntax.Tm_arrow uu____17514 in
                  FStar_Syntax_Syntax.mk uu____17513 in
                uu____17510 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____17531 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____17531 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____17558 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____17613 ->
                    let uu____17614 =
                      let uu____17623 =
                        let uu____17624 = FStar_Syntax_Subst.compress t3 in
                        uu____17624.FStar_Syntax_Syntax.n in
                      (uu____17623, tc) in
                    (match uu____17614 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____17649) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____17686) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____17725,FStar_Util.Inl uu____17726) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____17749 -> failwith "Impossible") in
              (match uu____17558 with
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
          let uu____17858 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____17858 with
          | (univ_names1,binders1,tc) ->
              let uu____17916 = FStar_Util.left tc in
              (univ_names1, binders1, uu____17916)
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
          let uu____17955 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____17955 with
          | (univ_names1,binders1,tc) ->
              let uu____18015 = FStar_Util.right tc in
              (univ_names1, binders1, uu____18015)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____18050 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____18050 with
           | (univ_names1,binders1,typ1) ->
               let uu___237_18078 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___237_18078.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___237_18078.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___237_18078.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___237_18078.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___238_18099 = s in
          let uu____18100 =
            let uu____18101 =
              let uu____18110 = FStar_List.map (elim_uvars env) sigs in
              (uu____18110, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____18101 in
          {
            FStar_Syntax_Syntax.sigel = uu____18100;
            FStar_Syntax_Syntax.sigrng =
              (uu___238_18099.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___238_18099.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___238_18099.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___238_18099.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____18127 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____18127 with
           | (univ_names1,uu____18145,typ1) ->
               let uu___239_18159 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___239_18159.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___239_18159.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___239_18159.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___239_18159.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____18165 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____18165 with
           | (univ_names1,uu____18183,typ1) ->
               let uu___240_18197 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___240_18197.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___240_18197.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___240_18197.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___240_18197.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____18231 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____18231 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____18254 =
                            let uu____18255 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____18255 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____18254 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___241_18258 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___241_18258.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___241_18258.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___242_18259 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___242_18259.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___242_18259.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___242_18259.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___242_18259.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___243_18271 = s in
          let uu____18272 =
            let uu____18273 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____18273 in
          {
            FStar_Syntax_Syntax.sigel = uu____18272;
            FStar_Syntax_Syntax.sigrng =
              (uu___243_18271.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___243_18271.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___243_18271.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___243_18271.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____18277 = elim_uvars_aux_t env us [] t in
          (match uu____18277 with
           | (us1,uu____18295,t1) ->
               let uu___244_18309 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___244_18309.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___244_18309.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___244_18309.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___244_18309.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____18310 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____18312 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____18312 with
           | (univs1,binders,signature) ->
               let uu____18340 =
                 let uu____18349 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____18349 with
                 | (univs_opening,univs2) ->
                     let uu____18376 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____18376) in
               (match uu____18340 with
                | (univs_opening,univs_closing) ->
                    let uu____18393 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____18399 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____18400 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____18399, uu____18400) in
                    (match uu____18393 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____18422 =
                           match uu____18422 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____18440 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____18440 with
                                | (us1,t1) ->
                                    let uu____18451 =
                                      let uu____18456 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____18463 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____18456, uu____18463) in
                                    (match uu____18451 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____18476 =
                                           let uu____18481 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____18490 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____18481, uu____18490) in
                                         (match uu____18476 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____18506 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____18506 in
                                              let uu____18507 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____18507 with
                                               | (uu____18528,uu____18529,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____18544 =
                                                       let uu____18545 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____18545 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____18544 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____18550 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____18550 with
                           | (uu____18563,uu____18564,t1) -> t1 in
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
                             | uu____18624 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____18641 =
                               let uu____18642 =
                                 FStar_Syntax_Subst.compress body in
                               uu____18642.FStar_Syntax_Syntax.n in
                             match uu____18641 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____18701 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____18730 =
                               let uu____18731 =
                                 FStar_Syntax_Subst.compress t in
                               uu____18731.FStar_Syntax_Syntax.n in
                             match uu____18730 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____18752) ->
                                 let uu____18773 = destruct_action_body body in
                                 (match uu____18773 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____18818 ->
                                 let uu____18819 = destruct_action_body t in
                                 (match uu____18819 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____18868 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____18868 with
                           | (action_univs,t) ->
                               let uu____18877 = destruct_action_typ_templ t in
                               (match uu____18877 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___245_18918 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___245_18918.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___245_18918.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___246_18920 = ed in
                           let uu____18921 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____18922 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____18923 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____18924 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____18925 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____18926 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____18927 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____18928 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____18929 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____18930 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____18931 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____18932 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____18933 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____18934 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___246_18920.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___246_18920.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____18921;
                             FStar_Syntax_Syntax.bind_wp = uu____18922;
                             FStar_Syntax_Syntax.if_then_else = uu____18923;
                             FStar_Syntax_Syntax.ite_wp = uu____18924;
                             FStar_Syntax_Syntax.stronger = uu____18925;
                             FStar_Syntax_Syntax.close_wp = uu____18926;
                             FStar_Syntax_Syntax.assert_p = uu____18927;
                             FStar_Syntax_Syntax.assume_p = uu____18928;
                             FStar_Syntax_Syntax.null_wp = uu____18929;
                             FStar_Syntax_Syntax.trivial = uu____18930;
                             FStar_Syntax_Syntax.repr = uu____18931;
                             FStar_Syntax_Syntax.return_repr = uu____18932;
                             FStar_Syntax_Syntax.bind_repr = uu____18933;
                             FStar_Syntax_Syntax.actions = uu____18934
                           } in
                         let uu___247_18937 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___247_18937.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___247_18937.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___247_18937.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___247_18937.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___165_18954 =
            match uu___165_18954 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____18981 = elim_uvars_aux_t env us [] t in
                (match uu____18981 with
                 | (us1,uu____19005,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___248_19024 = sub_eff in
            let uu____19025 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____19028 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___248_19024.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___248_19024.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____19025;
              FStar_Syntax_Syntax.lift = uu____19028
            } in
          let uu___249_19031 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___249_19031.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___249_19031.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___249_19031.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___249_19031.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____19041 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____19041 with
           | (univ_names1,binders1,comp1) ->
               let uu___250_19075 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___250_19075.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___250_19075.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___250_19075.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___250_19075.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____19086 -> s