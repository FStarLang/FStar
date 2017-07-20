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
    match projectee with | Clos _0 -> true | uu____269 -> false
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
    match projectee with | Univ _0 -> true | uu____337 -> false
let __proj__Univ__item___0: closure -> FStar_Syntax_Syntax.universe =
  fun projectee  -> match projectee with | Univ _0 -> _0
let uu___is_Dummy: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____350 -> false
type env = closure Prims.list
let closure_to_string: closure -> Prims.string =
  fun uu___138_356  ->
    match uu___138_356 with
    | Clos (uu____357,t,uu____359,uu____360) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____381 -> "Univ"
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
    match projectee with | Arg _0 -> true | uu____586 -> false
let __proj__Arg__item___0:
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Arg _0 -> _0
let uu___is_UnivArgs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____624 -> false
let __proj__UnivArgs__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____662 -> false
let __proj__MemoLazy__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0
let uu___is_Match: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____703 -> false
let __proj__Match__item___0:
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Abs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____747 -> false
let __proj__Abs__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____803 -> false
let __proj__App__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Meta: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____839 -> false
let __proj__Meta__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Meta _0 -> _0
let uu___is_Let: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____873 -> false
let __proj__Let__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Steps: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Steps _0 -> true | uu____921 -> false
let __proj__Steps__item___0:
  stack_elt ->
    (steps,primitive_step Prims.list,FStar_TypeChecker_Env.delta_level
                                       Prims.list)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Steps _0 -> _0
let uu___is_Debug: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____965 -> false
let __proj__Debug__item___0: stack_elt -> FStar_Syntax_Syntax.term =
  fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list
let mk:
  'Auu____982 .
    'Auu____982 ->
      FStar_Range.range -> 'Auu____982 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r
let set_memo:
  'Auu____1000 .
    'Auu____1000 FStar_Pervasives_Native.option FStar_ST.ref ->
      'Auu____1000 -> Prims.unit
  =
  fun r  ->
    fun t  ->
      let uu____1019 = FStar_ST.read r in
      match uu____1019 with
      | FStar_Pervasives_Native.Some uu____1026 ->
          failwith "Unexpected set_memo: thunk already evaluated"
      | FStar_Pervasives_Native.None  ->
          FStar_ST.write r (FStar_Pervasives_Native.Some t)
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____1039 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____1039 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___139_1047  ->
    match uu___139_1047 with
    | Arg (c,uu____1049,uu____1050) ->
        let uu____1051 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____1051
    | MemoLazy uu____1052 -> "MemoLazy"
    | Abs (uu____1059,bs,uu____1061,uu____1062,uu____1063) ->
        let uu____1068 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____1068
    | UnivArgs uu____1073 -> "UnivArgs"
    | Match uu____1080 -> "Match"
    | App (t,uu____1088,uu____1089) ->
        let uu____1090 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____1090
    | Meta (m,uu____1092) -> "Meta"
    | Let uu____1093 -> "Let"
    | Steps (uu____1102,uu____1103,uu____1104) -> "Steps"
    | Debug t ->
        let uu____1114 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____1114
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____1123 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____1123 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1141 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____1141 then f () else ()
let is_empty: 'Auu____1147 . 'Auu____1147 Prims.list -> Prims.bool =
  fun uu___140_1153  ->
    match uu___140_1153 with | [] -> true | uu____1156 -> false
let lookup_bvar:
  'Auu____1165 .
    'Auu____1165 Prims.list -> FStar_Syntax_Syntax.bv -> 'Auu____1165
  =
  fun env  ->
    fun x  ->
      try FStar_List.nth env x.FStar_Syntax_Syntax.index
      with
      | uu____1184 ->
          let uu____1185 =
            let uu____1186 = FStar_Syntax_Print.db_to_string x in
            FStar_Util.format1 "Failed to find %s\n" uu____1186 in
          failwith uu____1185
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
          let uu____1231 =
            FStar_List.fold_left
              (fun uu____1257  ->
                 fun u1  ->
                   match uu____1257 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____1282 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____1282 with
                        | (k_u,n1) ->
                            let uu____1297 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____1297
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____1231 with
          | (uu____1315,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____1340 = FStar_List.nth env x in
                 match uu____1340 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____1344 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____1353 ->
                   let uu____1354 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____1354
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____1360 when
              FStar_All.pipe_right cfg.steps
                (FStar_List.contains CheckNoUvars)
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1369 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1378 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1385 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____1385 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____1402 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____1402 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____1410 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____1418 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____1418 with
                                  | (uu____1423,m) -> n1 <= m)) in
                        if uu____1410 then rest1 else us1
                    | uu____1428 -> us1)
               | uu____1433 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1437 = aux u3 in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____1437 in
        let uu____1440 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____1440
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1442 = aux u in
           match uu____1442 with
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
          (fun uu____1562  ->
             let uu____1563 = FStar_Syntax_Print.tag_of_term t in
             let uu____1564 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1563
               uu____1564);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1565 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1569 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____1594 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____1595 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____1596 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____1597 ->
                  let uu____1614 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains CheckNoUvars) in
                  if uu____1614
                  then
                    let uu____1615 =
                      let uu____1616 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos in
                      let uu____1617 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____1616 uu____1617 in
                    failwith uu____1615
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____1620 =
                    let uu____1621 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____1621 in
                  mk uu____1620 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____1628 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____1628
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____1630 = lookup_bvar env x in
                  (match uu____1630 with
                   | Univ uu____1631 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____1635) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____1723 = closures_as_binders_delayed cfg env bs in
                  (match uu____1723 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____1757 =
                         let uu____1758 =
                           let uu____1775 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____1775) in
                         FStar_Syntax_Syntax.Tm_abs uu____1758 in
                       mk uu____1757 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____1806 = closures_as_binders_delayed cfg env bs in
                  (match uu____1806 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____1854 =
                    let uu____1867 =
                      let uu____1874 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____1874] in
                    closures_as_binders_delayed cfg env uu____1867 in
                  (match uu____1854 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____1896 =
                         let uu____1897 =
                           let uu____1904 =
                             let uu____1905 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____1905
                               FStar_Pervasives_Native.fst in
                           (uu____1904, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____1897 in
                       mk uu____1896 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____1996 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____1996
                    | FStar_Util.Inr c ->
                        let uu____2010 = close_comp cfg env c in
                        FStar_Util.Inr uu____2010 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____2026 =
                    let uu____2027 =
                      let uu____2054 = closure_as_term_delayed cfg env t11 in
                      (uu____2054, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____2027 in
                  mk uu____2026 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____2105 =
                    let uu____2106 =
                      let uu____2113 = closure_as_term_delayed cfg env t' in
                      let uu____2116 =
                        let uu____2117 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____2117 in
                      (uu____2113, uu____2116) in
                    FStar_Syntax_Syntax.Tm_meta uu____2106 in
                  mk uu____2105 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____2177 =
                    let uu____2178 =
                      let uu____2185 = closure_as_term_delayed cfg env t' in
                      let uu____2188 =
                        let uu____2189 =
                          let uu____2196 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____2196) in
                        FStar_Syntax_Syntax.Meta_monadic uu____2189 in
                      (uu____2185, uu____2188) in
                    FStar_Syntax_Syntax.Tm_meta uu____2178 in
                  mk uu____2177 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____2215 =
                    let uu____2216 =
                      let uu____2223 = closure_as_term_delayed cfg env t' in
                      let uu____2226 =
                        let uu____2227 =
                          let uu____2236 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____2236) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____2227 in
                      (uu____2223, uu____2226) in
                    FStar_Syntax_Syntax.Tm_meta uu____2216 in
                  mk uu____2215 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____2249 =
                    let uu____2250 =
                      let uu____2257 = closure_as_term_delayed cfg env t' in
                      (uu____2257, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____2250 in
                  mk uu____2249 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____2287  -> Dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let uu____2294 =
                    let uu____2305 = FStar_Syntax_Syntax.is_top_level [lb] in
                    if uu____2305
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       let uu____2324 =
                         closure_as_term cfg (Dummy :: env0) body in
                       ((FStar_Util.Inl
                           (let uu___155_2330 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___155_2330.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___155_2330.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____2324)) in
                  (match uu____2294 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___156_2346 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___156_2346.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___156_2346.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         } in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____2357,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____2392  -> fun env2  -> Dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____2399 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2399
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____2407  -> fun env2  -> Dummy :: env2) lbs
                          env_univs in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let nm =
                      let uu____2417 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2417
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         FStar_All.pipe_right
                           (let uu___157_2429 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___157_2429.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___157_2429.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41)) in
                    let uu___158_2430 = lb in
                    let uu____2431 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___158_2430.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___158_2430.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____2431
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____2449  -> fun env1  -> Dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____2528 =
                    match uu____2528 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____2593 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____2616 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____2682  ->
                                        fun uu____2683  ->
                                          match (uu____2682, uu____2683) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____2786 =
                                                norm_pat env3 p1 in
                                              (match uu____2786 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____2616 with
                               | (pats1,env3) ->
                                   ((let uu___159_2888 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___159_2888.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___160_2907 = x in
                                let uu____2908 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___160_2907.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___160_2907.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____2908
                                } in
                              ((let uu___161_2916 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___161_2916.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___162_2921 = x in
                                let uu____2922 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___162_2921.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___162_2921.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____2922
                                } in
                              ((let uu___163_2930 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___163_2930.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___164_2940 = x in
                                let uu____2941 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___164_2940.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___164_2940.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____2941
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___165_2950 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___165_2950.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____2953 = norm_pat env1 pat in
                        (match uu____2953 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____2988 =
                                     closure_as_term cfg env2 w in
                                   FStar_Pervasives_Native.Some uu____2988 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____2994 =
                    let uu____2995 =
                      let uu____3018 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____3018) in
                    FStar_Syntax_Syntax.Tm_match uu____2995 in
                  mk uu____2994 t1.FStar_Syntax_Syntax.pos))
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
        | uu____3100 -> closure_as_term cfg env t
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
        | uu____3124 ->
            FStar_List.map
              (fun uu____3143  ->
                 match uu____3143 with
                 | (x,imp) ->
                     let uu____3162 = closure_as_term_delayed cfg env x in
                     (uu____3162, imp)) args
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
        let uu____3178 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____3233  ->
                  fun uu____3234  ->
                    match (uu____3233, uu____3234) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___166_3316 = b in
                          let uu____3317 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___166_3316.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___166_3316.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____3317
                          } in
                        let env2 = Dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____3178 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____3398 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____3413 = closure_as_term_delayed cfg env t in
                 let uu____3414 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____3413 uu____3414
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____3427 = closure_as_term_delayed cfg env t in
                 let uu____3428 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____3427 uu____3428
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
                        (fun uu___141_3454  ->
                           match uu___141_3454 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____3458 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____3458
                           | f -> f)) in
                 let uu____3462 =
                   let uu___167_3463 = c1 in
                   let uu____3464 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____3464;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___167_3463.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____3462)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags  ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___142_3474  ->
            match uu___142_3474 with
            | FStar_Syntax_Syntax.DECREASES uu____3475 -> false
            | uu____3478 -> true))
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
                   (fun uu___143_3498  ->
                      match uu___143_3498 with
                      | FStar_Syntax_Syntax.DECREASES uu____3499 -> false
                      | uu____3502 -> true)) in
            let rc1 =
              let uu___168_3504 = rc in
              let uu____3505 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___168_3504.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____3505;
                FStar_Syntax_Syntax.residual_flags = flags
              } in
            FStar_Pervasives_Native.Some rc1
        | uu____3512 -> lopt
let built_in_primitive_steps: primitive_step Prims.list =
  let const_as_tm c p = mk (FStar_Syntax_Syntax.Tm_constant c) p in
  let int_as_const p i =
    let uu____3533 =
      let uu____3534 =
        let uu____3545 = FStar_Util.string_of_int i in
        (uu____3545, FStar_Pervasives_Native.None) in
      FStar_Const.Const_int uu____3534 in
    const_as_tm uu____3533 p in
  let bool_as_const p b = const_as_tm (FStar_Const.Const_bool b) p in
  let string_as_const p b =
    const_as_tm
      (FStar_Const.Const_string ((FStar_Util.bytes_of_string b), p)) p in
  let arg_as_int uu____3581 =
    match uu____3581 with
    | (a,uu____3589) ->
        let uu____3592 =
          let uu____3593 = FStar_Syntax_Subst.compress a in
          uu____3593.FStar_Syntax_Syntax.n in
        (match uu____3592 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (i,FStar_Pervasives_Native.None )) ->
             let uu____3609 = FStar_Util.int_of_string i in
             FStar_Pervasives_Native.Some uu____3609
         | uu____3610 -> FStar_Pervasives_Native.None) in
  let arg_as_bounded_int uu____3624 =
    match uu____3624 with
    | (a,uu____3636) ->
        let uu____3643 =
          let uu____3644 = FStar_Syntax_Subst.compress a in
          uu____3644.FStar_Syntax_Syntax.n in
        (match uu____3643 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____3654;
                FStar_Syntax_Syntax.vars = uu____3655;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____3657;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____3658;_},uu____3659)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____3698 =
               let uu____3703 = FStar_Util.int_of_string i in
               (fv1, uu____3703) in
             FStar_Pervasives_Native.Some uu____3698
         | uu____3708 -> FStar_Pervasives_Native.None) in
  let arg_as_bool uu____3722 =
    match uu____3722 with
    | (a,uu____3730) ->
        let uu____3733 =
          let uu____3734 = FStar_Syntax_Subst.compress a in
          uu____3734.FStar_Syntax_Syntax.n in
        (match uu____3733 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
             FStar_Pervasives_Native.Some b
         | uu____3740 -> FStar_Pervasives_Native.None) in
  let arg_as_char uu____3750 =
    match uu____3750 with
    | (a,uu____3758) ->
        let uu____3761 =
          let uu____3762 = FStar_Syntax_Subst.compress a in
          uu____3762.FStar_Syntax_Syntax.n in
        (match uu____3761 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
             FStar_Pervasives_Native.Some c
         | uu____3768 -> FStar_Pervasives_Native.None) in
  let arg_as_string uu____3778 =
    match uu____3778 with
    | (a,uu____3786) ->
        let uu____3789 =
          let uu____3790 = FStar_Syntax_Subst.compress a in
          uu____3790.FStar_Syntax_Syntax.n in
        (match uu____3789 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (bytes,uu____3796)) ->
             FStar_Pervasives_Native.Some (FStar_Util.string_of_bytes bytes)
         | uu____3801 -> FStar_Pervasives_Native.None) in
  let arg_as_list f uu____3827 =
    match uu____3827 with
    | (a,uu____3841) ->
        let rec sequence l =
          match l with
          | [] -> FStar_Pervasives_Native.Some []
          | (FStar_Pervasives_Native.None )::uu____3870 ->
              FStar_Pervasives_Native.None
          | (FStar_Pervasives_Native.Some x)::xs ->
              let uu____3887 = sequence xs in
              (match uu____3887 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some xs' ->
                   FStar_Pervasives_Native.Some (x :: xs')) in
        let uu____3907 = FStar_Syntax_Util.list_elements a in
        (match uu____3907 with
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some elts ->
             let uu____3925 =
               FStar_List.map
                 (fun x  ->
                    let uu____3935 = FStar_Syntax_Syntax.as_arg x in
                    f uu____3935) elts in
             sequence uu____3925) in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____3973 = f a in FStar_Pervasives_Native.Some uu____3973
    | uu____3974 -> FStar_Pervasives_Native.None in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4024 = f a0 a1 in FStar_Pervasives_Native.Some uu____4024
    | uu____4025 -> FStar_Pervasives_Native.None in
  let unary_op as_a f r args =
    let uu____4074 = FStar_List.map as_a args in lift_unary (f r) uu____4074 in
  let binary_op as_a f r args =
    let uu____4130 = FStar_List.map as_a args in lift_binary (f r) uu____4130 in
  let as_primitive_step uu____4154 =
    match uu____4154 with
    | (l,arity,f) ->
        { name = l; arity; strong_reduction_ok = true; interpretation = f } in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  -> fun x  -> let uu____4202 = f x in int_as_const r uu____4202) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  -> let uu____4230 = f x y in int_as_const r uu____4230) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  -> fun x  -> let uu____4251 = f x in bool_as_const r uu____4251) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  -> let uu____4279 = f x y in bool_as_const r uu____4279) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  -> let uu____4307 = f x y in string_as_const r uu____4307) in
  let list_of_string' rng s =
    let name l =
      let uu____4321 =
        let uu____4322 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____4322 in
      mk uu____4321 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____4332 =
      let uu____4335 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____4335 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____4332 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in int_as_const rng r in
  let string_concat' rng args =
    match args with
    | a1::a2::[] ->
        let uu____4410 = arg_as_string a1 in
        (match uu____4410 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4416 = arg_as_list arg_as_string a2 in
             (match uu____4416 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____4429 = string_as_const rng r in
                  FStar_Pervasives_Native.Some uu____4429
              | uu____4430 -> FStar_Pervasives_Native.None)
         | uu____4435 -> FStar_Pervasives_Native.None)
    | uu____4438 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____4452 = FStar_Util.string_of_int i in
    string_as_const rng uu____4452 in
  let string_of_bool1 rng b =
    string_as_const rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____4468 = FStar_Util.string_of_int i in
    string_as_const rng uu____4468 in
  let string_of_bool2 rng b =
    string_as_const rng (if b then "true" else "false") in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r in
  let range_of1 uu____4498 args =
    match args with
    | uu____4510::(t,uu____4512)::[] ->
        let uu____4541 = term_of_range t.FStar_Syntax_Syntax.pos in
        FStar_Pervasives_Native.Some uu____4541
    | uu____4546 -> FStar_Pervasives_Native.None in
  let set_range_of1 r args =
    match args with
    | uu____4584::(t,uu____4586)::({
                                     FStar_Syntax_Syntax.n =
                                       FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_range r1);
                                     FStar_Syntax_Syntax.pos = uu____4588;
                                     FStar_Syntax_Syntax.vars = uu____4589;_},uu____4590)::[]
        ->
        FStar_Pervasives_Native.Some
          (let uu___169_4632 = t in
           {
             FStar_Syntax_Syntax.n = (uu___169_4632.FStar_Syntax_Syntax.n);
             FStar_Syntax_Syntax.pos = r1;
             FStar_Syntax_Syntax.vars =
               (uu___169_4632.FStar_Syntax_Syntax.vars)
           })
    | uu____4635 -> FStar_Pervasives_Native.None in
  let mk_range1 r args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____4716 =
          let uu____4737 = arg_as_string fn in
          let uu____4740 = arg_as_int from_line in
          let uu____4743 = arg_as_int from_col in
          let uu____4746 = arg_as_int to_line in
          let uu____4749 = arg_as_int to_col in
          (uu____4737, uu____4740, uu____4743, uu____4746, uu____4749) in
        (match uu____4716 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r1 =
               let uu____4780 = FStar_Range.mk_pos from_l from_c in
               let uu____4781 = FStar_Range.mk_pos to_l to_c in
               FStar_Range.mk_range fn1 uu____4780 uu____4781 in
             let uu____4782 = term_of_range r1 in
             FStar_Pervasives_Native.Some uu____4782
         | uu____4787 -> FStar_Pervasives_Native.None)
    | uu____4808 -> FStar_Pervasives_Native.None in
  let decidable_eq neg rng args =
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) rng in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) rng in
    match args with
    | (_typ,uu____4838)::(a1,uu____4840)::(a2,uu____4842)::[] ->
        let uu____4879 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4879 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____4892 -> FStar_Pervasives_Native.None)
    | uu____4893 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____4911 =
      let uu____4926 =
        let uu____4941 =
          let uu____4956 =
            let uu____4971 =
              let uu____4986 =
                let uu____5001 =
                  let uu____5016 =
                    let uu____5031 =
                      let uu____5046 =
                        let uu____5061 =
                          let uu____5076 =
                            let uu____5091 =
                              let uu____5106 =
                                let uu____5121 =
                                  let uu____5136 =
                                    let uu____5151 =
                                      let uu____5166 =
                                        let uu____5181 =
                                          let uu____5196 =
                                            let uu____5211 =
                                              let uu____5224 =
                                                FStar_Parser_Const.p2l
                                                  ["FStar";
                                                  "String";
                                                  "list_of_string"] in
                                              (uu____5224,
                                                (Prims.parse_int "1"),
                                                (unary_op arg_as_string
                                                   list_of_string')) in
                                            let uu____5231 =
                                              let uu____5246 =
                                                let uu____5259 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "string_of_list"] in
                                                (uu____5259,
                                                  (Prims.parse_int "1"),
                                                  (unary_op
                                                     (arg_as_list arg_as_char)
                                                     string_of_list')) in
                                              let uu____5268 =
                                                let uu____5283 =
                                                  let uu____5302 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "concat"] in
                                                  (uu____5302,
                                                    (Prims.parse_int "2"),
                                                    string_concat') in
                                                let uu____5315 =
                                                  let uu____5336 =
                                                    let uu____5357 =
                                                      FStar_Parser_Const.p2l
                                                        ["Prims"; "range_of"] in
                                                    (uu____5357,
                                                      (Prims.parse_int "2"),
                                                      range_of1) in
                                                  let uu____5372 =
                                                    let uu____5395 =
                                                      let uu____5416 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "set_range_of"] in
                                                      (uu____5416,
                                                        (Prims.parse_int "3"),
                                                        set_range_of1) in
                                                    let uu____5431 =
                                                      let uu____5454 =
                                                        let uu____5473 =
                                                          FStar_Parser_Const.p2l
                                                            ["Prims";
                                                            "mk_range"] in
                                                        (uu____5473,
                                                          (Prims.parse_int
                                                             "5"), mk_range1) in
                                                      [uu____5454] in
                                                    uu____5395 :: uu____5431 in
                                                  uu____5336 :: uu____5372 in
                                                uu____5283 :: uu____5315 in
                                              uu____5246 :: uu____5268 in
                                            uu____5211 :: uu____5231 in
                                          (FStar_Parser_Const.op_notEq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq true)) ::
                                            uu____5196 in
                                        (FStar_Parser_Const.op_Eq,
                                          (Prims.parse_int "3"),
                                          (decidable_eq false)) :: uu____5181 in
                                      (FStar_Parser_Const.string_compare,
                                        (Prims.parse_int "2"),
                                        (binary_op arg_as_string
                                           string_compare'))
                                        :: uu____5166 in
                                    (FStar_Parser_Const.string_of_bool_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_bool string_of_bool2))
                                      :: uu____5151 in
                                  (FStar_Parser_Const.string_of_int_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_int string_of_int2)) ::
                                    uu____5136 in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____5121 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5106 in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____5091 in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____5076 in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____5061 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____5046 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
                      :: uu____5031 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____5016 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____5001 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____4986 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____4971 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____4956 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____4941 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____4926 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____4911 in
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
      let uu____6080 =
        let uu____6081 =
          let uu____6082 = FStar_Syntax_Syntax.as_arg c in [uu____6082] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6081 in
      uu____6080 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____6117 =
              let uu____6130 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____6130, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____6149  ->
                        fun uu____6150  ->
                          match (uu____6149, uu____6150) with
                          | ((int_to_t1,x),(uu____6169,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____6179 =
              let uu____6194 =
                let uu____6207 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____6207, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____6226  ->
                          fun uu____6227  ->
                            match (uu____6226, uu____6227) with
                            | ((int_to_t1,x),(uu____6246,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____6256 =
                let uu____6271 =
                  let uu____6284 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____6284, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____6303  ->
                            fun uu____6304  ->
                              match (uu____6303, uu____6304) with
                              | ((int_to_t1,x),(uu____6323,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____6271] in
              uu____6194 :: uu____6256 in
            uu____6117 :: uu____6179)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop r args =
    match args with
    | (_typ,uu____6419)::(a1,uu____6421)::(a2,uu____6423)::[] ->
        let uu____6460 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6460 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___170_6466 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___170_6466.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___170_6466.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___171_6470 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___171_6470.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___171_6470.FStar_Syntax_Syntax.vars)
                })
         | uu____6471 -> FStar_Pervasives_Native.None)
    | (_typ,uu____6473)::uu____6474::(a1,uu____6476)::(a2,uu____6478)::[] ->
        let uu____6527 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6527 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___170_6533 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___170_6533.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___170_6533.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___171_6537 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___171_6537.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___171_6537.FStar_Syntax_Syntax.vars)
                })
         | uu____6538 -> FStar_Pervasives_Native.None)
    | uu____6539 -> failwith "Unexpected number of arguments" in
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
      let uu____6552 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops cfg.steps) in
      if uu____6552
      then tm
      else
        (let uu____6554 = FStar_Syntax_Util.head_and_args tm in
         match uu____6554 with
         | (head1,args) ->
             let uu____6591 =
               let uu____6592 = FStar_Syntax_Util.un_uinst head1 in
               uu____6592.FStar_Syntax_Syntax.n in
             (match uu____6591 with
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____6596 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps in
                  (match uu____6596 with
                   | FStar_Pervasives_Native.None  -> tm
                   | FStar_Pervasives_Native.Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then tm
                       else
                         (let uu____6609 =
                            prim_step.interpretation
                              head1.FStar_Syntax_Syntax.pos args in
                          match uu____6609 with
                          | FStar_Pervasives_Native.None  -> tm
                          | FStar_Pervasives_Native.Some reduced -> reduced))
              | uu____6613 -> tm))
let reduce_equality:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___172_6624 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___172_6624.tcenv);
           delta_level = (uu___172_6624.delta_level);
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
        let uu___173_6648 = t in
        {
          FStar_Syntax_Syntax.n = (uu___173_6648.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___173_6648.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid ->
            FStar_Pervasives_Native.Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid ->
            FStar_Pervasives_Native.Some false
        | uu____6665 -> FStar_Pervasives_Native.None in
      let simplify arg = ((simp_t (FStar_Pervasives_Native.fst arg)), arg) in
      let tm1 = reduce_primops cfg tm in
      let uu____6705 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps) in
      if uu____6705
      then tm1
      else
        (match tm1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.pos = uu____6708;
                     FStar_Syntax_Syntax.vars = uu____6709;_},uu____6710);
                FStar_Syntax_Syntax.pos = uu____6711;
                FStar_Syntax_Syntax.vars = uu____6712;_},args)
             ->
             let uu____6738 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
             if uu____6738
             then
               let uu____6739 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____6739 with
                | (FStar_Pervasives_Native.Some (true ),uu____6794)::
                    (uu____6795,(arg,uu____6797))::[] -> arg
                | (uu____6862,(arg,uu____6864))::(FStar_Pervasives_Native.Some
                                                  (true ),uu____6865)::[]
                    -> arg
                | (FStar_Pervasives_Native.Some (false ),uu____6930)::uu____6931::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____6994::(FStar_Pervasives_Native.Some (false
                               ),uu____6995)::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____7058 -> tm1)
             else
               (let uu____7074 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
                if uu____7074
                then
                  let uu____7075 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____7075 with
                  | (FStar_Pervasives_Native.Some (true ),uu____7130)::uu____7131::[]
                      -> w FStar_Syntax_Util.t_true
                  | uu____7194::(FStar_Pervasives_Native.Some (true
                                 ),uu____7195)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____7258)::
                      (uu____7259,(arg,uu____7261))::[] -> arg
                  | (uu____7326,(arg,uu____7328))::(FStar_Pervasives_Native.Some
                                                    (false ),uu____7329)::[]
                      -> arg
                  | uu____7394 -> tm1
                else
                  (let uu____7410 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.imp_lid in
                   if uu____7410
                   then
                     let uu____7411 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____7411 with
                     | uu____7466::(FStar_Pervasives_Native.Some (true
                                    ),uu____7467)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____7530)::uu____7531::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____7594)::
                         (uu____7595,(arg,uu____7597))::[] -> arg
                     | (uu____7662,(p,uu____7664))::(uu____7665,(q,uu____7667))::[]
                         ->
                         let uu____7732 = FStar_Syntax_Util.term_eq p q in
                         (if uu____7732
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____7734 -> tm1
                   else
                     (let uu____7750 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____7750
                      then
                        let uu____7751 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____7751 with
                        | (FStar_Pervasives_Native.Some (true ),uu____7806)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____7845)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____7884 -> tm1
                      else
                        (let uu____7900 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____7900
                         then
                           match args with
                           | (t,uu____7902)::[] ->
                               let uu____7919 =
                                 let uu____7920 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____7920.FStar_Syntax_Syntax.n in
                               (match uu____7919 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____7923::[],body,uu____7925) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____7952 -> tm1)
                                | uu____7955 -> tm1)
                           | (uu____7956,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____7957))::
                               (t,uu____7959)::[] ->
                               let uu____7998 =
                                 let uu____7999 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____7999.FStar_Syntax_Syntax.n in
                               (match uu____7998 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____8002::[],body,uu____8004) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____8031 -> tm1)
                                | uu____8034 -> tm1)
                           | uu____8035 -> tm1
                         else
                           (let uu____8045 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____8045
                            then
                              match args with
                              | (t,uu____8047)::[] ->
                                  let uu____8064 =
                                    let uu____8065 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____8065.FStar_Syntax_Syntax.n in
                                  (match uu____8064 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____8068::[],body,uu____8070) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____8097 -> tm1)
                                   | uu____8100 -> tm1)
                              | (uu____8101,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____8102))::
                                  (t,uu____8104)::[] ->
                                  let uu____8143 =
                                    let uu____8144 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____8144.FStar_Syntax_Syntax.n in
                                  (match uu____8143 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____8147::[],body,uu____8149) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____8176 -> tm1)
                                   | uu____8179 -> tm1)
                              | uu____8180 -> tm1
                            else reduce_equality cfg tm1)))))
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                FStar_Syntax_Syntax.pos = uu____8191;
                FStar_Syntax_Syntax.vars = uu____8192;_},args)
             ->
             let uu____8214 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
             if uu____8214
             then
               let uu____8215 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____8215 with
                | (FStar_Pervasives_Native.Some (true ),uu____8270)::
                    (uu____8271,(arg,uu____8273))::[] -> arg
                | (uu____8338,(arg,uu____8340))::(FStar_Pervasives_Native.Some
                                                  (true ),uu____8341)::[]
                    -> arg
                | (FStar_Pervasives_Native.Some (false ),uu____8406)::uu____8407::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____8470::(FStar_Pervasives_Native.Some (false
                               ),uu____8471)::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____8534 -> tm1)
             else
               (let uu____8550 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
                if uu____8550
                then
                  let uu____8551 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____8551 with
                  | (FStar_Pervasives_Native.Some (true ),uu____8606)::uu____8607::[]
                      -> w FStar_Syntax_Util.t_true
                  | uu____8670::(FStar_Pervasives_Native.Some (true
                                 ),uu____8671)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____8734)::
                      (uu____8735,(arg,uu____8737))::[] -> arg
                  | (uu____8802,(arg,uu____8804))::(FStar_Pervasives_Native.Some
                                                    (false ),uu____8805)::[]
                      -> arg
                  | uu____8870 -> tm1
                else
                  (let uu____8886 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.imp_lid in
                   if uu____8886
                   then
                     let uu____8887 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____8887 with
                     | uu____8942::(FStar_Pervasives_Native.Some (true
                                    ),uu____8943)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____9006)::uu____9007::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____9070)::
                         (uu____9071,(arg,uu____9073))::[] -> arg
                     | (uu____9138,(p,uu____9140))::(uu____9141,(q,uu____9143))::[]
                         ->
                         let uu____9208 = FStar_Syntax_Util.term_eq p q in
                         (if uu____9208
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____9210 -> tm1
                   else
                     (let uu____9226 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____9226
                      then
                        let uu____9227 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____9227 with
                        | (FStar_Pervasives_Native.Some (true ),uu____9282)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____9321)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____9360 -> tm1
                      else
                        (let uu____9376 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____9376
                         then
                           match args with
                           | (t,uu____9378)::[] ->
                               let uu____9395 =
                                 let uu____9396 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____9396.FStar_Syntax_Syntax.n in
                               (match uu____9395 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____9399::[],body,uu____9401) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____9428 -> tm1)
                                | uu____9431 -> tm1)
                           | (uu____9432,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____9433))::
                               (t,uu____9435)::[] ->
                               let uu____9474 =
                                 let uu____9475 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____9475.FStar_Syntax_Syntax.n in
                               (match uu____9474 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____9478::[],body,uu____9480) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____9507 -> tm1)
                                | uu____9510 -> tm1)
                           | uu____9511 -> tm1
                         else
                           (let uu____9521 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____9521
                            then
                              match args with
                              | (t,uu____9523)::[] ->
                                  let uu____9540 =
                                    let uu____9541 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____9541.FStar_Syntax_Syntax.n in
                                  (match uu____9540 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____9544::[],body,uu____9546) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____9573 -> tm1)
                                   | uu____9576 -> tm1)
                              | (uu____9577,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____9578))::
                                  (t,uu____9580)::[] ->
                                  let uu____9619 =
                                    let uu____9620 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____9620.FStar_Syntax_Syntax.n in
                                  (match uu____9619 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____9623::[],body,uu____9625) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____9652 -> tm1)
                                   | uu____9655 -> tm1)
                              | uu____9656 -> tm1
                            else reduce_equality cfg tm1)))))
         | uu____9666 -> tm1)
let is_norm_request:
  'Auu____9673 .
    FStar_Syntax_Syntax.term -> 'Auu____9673 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____9686 =
        let uu____9693 =
          let uu____9694 = FStar_Syntax_Util.un_uinst hd1 in
          uu____9694.FStar_Syntax_Syntax.n in
        (uu____9693, args) in
      match uu____9686 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____9700::uu____9701::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____9705::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | uu____9708 -> false
let get_norm_request:
  'Auu____9721 'Auu____9722 .
    ('Auu____9722,'Auu____9721) FStar_Pervasives_Native.tuple2 Prims.list ->
      'Auu____9722
  =
  fun args  ->
    match args with
    | uu____9739::(tm,uu____9741)::[] -> tm
    | (tm,uu____9759)::[] -> tm
    | uu____9768 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___144_9780  ->
    match uu___144_9780 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.pos = uu____9783;
           FStar_Syntax_Syntax.vars = uu____9784;_},uu____9785,uu____9786))::uu____9787
        -> true
    | uu____9794 -> false
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
            (fun uu____9929  ->
               let uu____9930 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____9931 = FStar_Syntax_Print.term_to_string t1 in
               let uu____9932 =
                 let uu____9933 =
                   let uu____9936 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9936 in
                 stack_to_string uu____9933 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____9930
                 uu____9931 uu____9932);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____9959 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____9984 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____10001 =
                 let uu____10002 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____10003 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____10002 uu____10003 in
               failwith uu____10001
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____10004 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____10021 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____10022 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10023;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____10024;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10027;
                 FStar_Syntax_Syntax.fv_delta = uu____10028;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10029;
                 FStar_Syntax_Syntax.fv_delta = uu____10030;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____10031);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (FStar_Syntax_Util.is_fstar_tactics_embed hd1) ||
                 (FStar_Syntax_Util.is_fstar_tactics_by_tactic hd1)
               ->
               let args1 = closures_as_args_delayed cfg env args in
               let hd2 = closure_as_term cfg env hd1 in
               let t2 =
                 let uu___174_10073 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___174_10073.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___174_10073.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____10106 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____10106) && (is_norm_request hd1 args))
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
                 let uu___175_10122 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___175_10122.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___175_10122.primitive_steps)
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
                  FStar_Syntax_Syntax.pos = uu____10130;
                  FStar_Syntax_Syntax.vars = uu____10131;_},a1::a2::rest)
               ->
               let uu____10179 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____10179 with
                | (hd1,uu____10195) ->
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
                    (FStar_Const.Const_reflect uu____10260);
                  FStar_Syntax_Syntax.pos = uu____10261;
                  FStar_Syntax_Syntax.vars = uu____10262;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____10294 = FStar_List.tl stack1 in
               norm cfg env uu____10294 (FStar_Pervasives_Native.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____10297;
                  FStar_Syntax_Syntax.vars = uu____10298;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____10330 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____10330 with
                | (reify_head,uu____10346) ->
                    let a1 =
                      let uu____10368 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (FStar_Pervasives_Native.fst a) in
                      FStar_Syntax_Subst.compress uu____10368 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____10371);
                            FStar_Syntax_Syntax.pos = uu____10372;
                            FStar_Syntax_Syntax.vars = uu____10373;_},a2::[])
                         ->
                         norm cfg env stack1 (FStar_Pervasives_Native.fst a2)
                     | uu____10407 ->
                         let stack2 =
                           (App
                              (reify_head, FStar_Pervasives_Native.None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____10417 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____10417
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____10424 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____10424
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____10427 =
                      let uu____10434 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____10434, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____10427 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___145_10448  ->
                         match uu___145_10448 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____10451 =
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
                 if uu____10451 then false else should_delta in
               if Prims.op_Negation should_delta1
               then rebuild cfg env stack1 t1
               else
                 (let r_env =
                    let uu____10455 = FStar_Syntax_Syntax.range_of_fv f in
                    FStar_TypeChecker_Env.set_range cfg.tcenv uu____10455 in
                  let uu____10456 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  match uu____10456 with
                  | FStar_Pervasives_Native.None  ->
                      (log cfg
                         (fun uu____10469  ->
                            FStar_Util.print "Tm_fvar case 2\n" []);
                       rebuild cfg env stack1 t1)
                  | FStar_Pervasives_Native.Some (us,t2) ->
                      (log cfg
                         (fun uu____10480  ->
                            let uu____10481 =
                              FStar_Syntax_Print.term_to_string t0 in
                            let uu____10482 =
                              FStar_Syntax_Print.term_to_string t2 in
                            FStar_Util.print2 ">>> Unfolded %s to %s\n"
                              uu____10481 uu____10482);
                       (let t3 =
                          let uu____10484 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 (UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant)) in
                          if uu____10484
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
                          | (UnivArgs (us',uu____10494))::stack2 ->
                              let env1 =
                                FStar_All.pipe_right us'
                                  (FStar_List.fold_left
                                     (fun env1  -> fun u  -> (Univ u) :: env1)
                                     env) in
                              norm cfg env1 stack2 t3
                          | uu____10517 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack1 t3
                          | uu____10518 ->
                              let uu____10519 =
                                let uu____10520 =
                                  FStar_Syntax_Print.lid_to_string
                                    (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                FStar_Util.format1
                                  "Impossible: missing universe instantiation on %s"
                                  uu____10520 in
                              failwith uu____10519
                        else norm cfg env stack1 t3)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____10523 = lookup_bvar env x in
               (match uu____10523 with
                | Univ uu____10524 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____10549 = FStar_ST.read r in
                      (match uu____10549 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____10584  ->
                                 let uu____10585 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____10586 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____10585
                                   uu____10586);
                            (let uu____10587 =
                               let uu____10588 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____10588.FStar_Syntax_Syntax.n in
                             match uu____10587 with
                             | FStar_Syntax_Syntax.Tm_abs uu____10591 ->
                                 norm cfg env2 stack1 t'
                             | uu____10608 -> rebuild cfg env2 stack1 t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____10642)::uu____10643 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____10652)::uu____10653 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____10663,uu____10664))::stack_rest ->
                    (match c with
                     | Univ uu____10668 -> norm cfg (c :: env) stack_rest t1
                     | uu____10669 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____10674::[] ->
                              (match lopt with
                               | FStar_Pervasives_Native.None  when
                                   FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____10690  ->
                                         let uu____10691 =
                                           closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____10691);
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
                                           (fun uu___146_10696  ->
                                              match uu___146_10696 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____10697 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____10701  ->
                                         let uu____10702 =
                                           closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____10702);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____10703 when
                                   (FStar_All.pipe_right cfg.steps
                                      (FStar_List.contains Reify))
                                     ||
                                     (FStar_All.pipe_right cfg.steps
                                        (FStar_List.contains CheckNoUvars))
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____10706 ->
                                   let cfg1 =
                                     let uu___176_10710 = cfg in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___176_10710.tcenv);
                                       delta_level =
                                         (uu___176_10710.delta_level);
                                       primitive_steps =
                                         (uu___176_10710.primitive_steps)
                                     } in
                                   let uu____10711 =
                                     closure_as_term cfg1 env t1 in
                                   rebuild cfg1 env stack1 uu____10711)
                          | uu____10712::tl1 ->
                              (log cfg
                                 (fun uu____10731  ->
                                    let uu____10732 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10732);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___177_10762 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___177_10762.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____10783  ->
                          let uu____10784 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____10784);
                     norm cfg env stack2 t1)
                | (Debug uu____10785)::uu____10786 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____10789 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____10789
                    else
                      (let uu____10791 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____10791 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10815  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____10831 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____10831
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____10841 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____10841)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___178_10846 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___178_10846.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___178_10846.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10847 -> lopt in
                           (log cfg
                              (fun uu____10853  ->
                                 let uu____10854 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10854);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___179_10867 = cfg in
                               let uu____10868 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___179_10867.steps);
                                 tcenv = (uu___179_10867.tcenv);
                                 delta_level = (uu___179_10867.delta_level);
                                 primitive_steps = uu____10868
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____10877)::uu____10878 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____10885 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____10885
                    else
                      (let uu____10887 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____10887 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10911  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____10927 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____10927
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____10937 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____10937)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___178_10942 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___178_10942.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___178_10942.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10943 -> lopt in
                           (log cfg
                              (fun uu____10949  ->
                                 let uu____10950 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10950);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___179_10963 = cfg in
                               let uu____10964 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___179_10963.steps);
                                 tcenv = (uu___179_10963.tcenv);
                                 delta_level = (uu___179_10963.delta_level);
                                 primitive_steps = uu____10964
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____10973)::uu____10974 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____10985 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____10985
                    else
                      (let uu____10987 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____10987 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11011  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11027 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11027
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11037 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11037)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___178_11042 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___178_11042.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___178_11042.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11043 -> lopt in
                           (log cfg
                              (fun uu____11049  ->
                                 let uu____11050 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11050);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___179_11063 = cfg in
                               let uu____11064 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___179_11063.steps);
                                 tcenv = (uu___179_11063.tcenv);
                                 delta_level = (uu___179_11063.delta_level);
                                 primitive_steps = uu____11064
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____11073)::uu____11074 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11083 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11083
                    else
                      (let uu____11085 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11085 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11109  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11125 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11125
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11135 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11135)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___178_11140 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___178_11140.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___178_11140.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11141 -> lopt in
                           (log cfg
                              (fun uu____11147  ->
                                 let uu____11148 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11148);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___179_11161 = cfg in
                               let uu____11162 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___179_11161.steps);
                                 tcenv = (uu___179_11161.tcenv);
                                 delta_level = (uu___179_11161.delta_level);
                                 primitive_steps = uu____11162
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____11171)::uu____11172 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11187 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11187
                    else
                      (let uu____11189 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11189 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11213  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11229 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11229
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11239 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11239)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___178_11244 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___178_11244.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___178_11244.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11245 -> lopt in
                           (log cfg
                              (fun uu____11251  ->
                                 let uu____11252 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11252);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___179_11265 = cfg in
                               let uu____11266 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___179_11265.steps);
                                 tcenv = (uu___179_11265.tcenv);
                                 delta_level = (uu___179_11265.delta_level);
                                 primitive_steps = uu____11266
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11275 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11275
                    else
                      (let uu____11277 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11277 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11301  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11317 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11317
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11327 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11327)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___178_11332 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___178_11332.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___178_11332.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11333 -> lopt in
                           (log cfg
                              (fun uu____11339  ->
                                 let uu____11340 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11340);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___179_11353 = cfg in
                               let uu____11354 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___179_11353.steps);
                                 tcenv = (uu___179_11353.tcenv);
                                 delta_level = (uu___179_11353.delta_level);
                                 primitive_steps = uu____11354
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
                      (fun uu____11401  ->
                         fun stack2  ->
                           match uu____11401 with
                           | (a,aq) ->
                               let uu____11413 =
                                 let uu____11414 =
                                   let uu____11421 =
                                     let uu____11422 =
                                       let uu____11441 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____11441, false) in
                                     Clos uu____11422 in
                                   (uu____11421, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____11414 in
                               uu____11413 :: stack2) args) in
               (log cfg
                  (fun uu____11481  ->
                     let uu____11482 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____11482);
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
                             ((let uu___180_11506 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___180_11506.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___180_11506.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____11507 ->
                      let uu____11512 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11512)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____11515 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____11515 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____11540 =
                          let uu____11541 =
                            let uu____11548 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___181_11550 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___181_11550.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___181_11550.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____11548) in
                          FStar_Syntax_Syntax.Tm_refine uu____11541 in
                        mk uu____11540 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____11569 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____11569
               else
                 (let uu____11571 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____11571 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____11579 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____11591  -> Dummy :: env1) env) in
                        norm_comp cfg uu____11579 c1 in
                      let t2 =
                        let uu____11601 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____11601 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____11660)::uu____11661 -> norm cfg env stack1 t11
                | (Arg uu____11670)::uu____11671 -> norm cfg env stack1 t11
                | (App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____11680;
                       FStar_Syntax_Syntax.vars = uu____11681;_},uu____11682,uu____11683))::uu____11684
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____11691)::uu____11692 ->
                    norm cfg env stack1 t11
                | uu____11701 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____11705  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____11722 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____11722
                        | FStar_Util.Inr c ->
                            let uu____11730 = norm_comp cfg env c in
                            FStar_Util.Inr uu____11730 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____11736 =
                        let uu____11737 =
                          let uu____11738 =
                            let uu____11765 = FStar_Syntax_Util.unascribe t12 in
                            (uu____11765, (tc1, tacopt1), l) in
                          FStar_Syntax_Syntax.Tm_ascribed uu____11738 in
                        mk uu____11737 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____11736)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____11841,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____11842;
                               FStar_Syntax_Syntax.lbunivs = uu____11843;
                               FStar_Syntax_Syntax.lbtyp = uu____11844;
                               FStar_Syntax_Syntax.lbeff = uu____11845;
                               FStar_Syntax_Syntax.lbdef = uu____11846;_}::uu____11847),uu____11848)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____11884 =
                 (let uu____11887 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____11887) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____11889 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____11889))) in
               if uu____11884
               then
                 let env1 =
                   let uu____11893 =
                     let uu____11894 =
                       let uu____11913 =
                         FStar_Util.mk_ref FStar_Pervasives_Native.None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____11913,
                         false) in
                     Clos uu____11894 in
                   uu____11893 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____11953 =
                    let uu____11958 =
                      let uu____11959 =
                        let uu____11960 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____11960
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____11959] in
                    FStar_Syntax_Subst.open_term uu____11958 body in
                  match uu____11953 with
                  | (bs,body1) ->
                      let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                      let lbname =
                        let x =
                          let uu____11974 = FStar_List.hd bs in
                          FStar_Pervasives_Native.fst uu____11974 in
                        FStar_Util.Inl
                          (let uu___182_11984 = x in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___182_11984.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___182_11984.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = ty
                           }) in
                      let lb1 =
                        let uu___183_11986 = lb in
                        let uu____11987 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = lbname;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___183_11986.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = ty;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___183_11986.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____11987
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____12004  -> Dummy :: env1)
                             env) in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let ((true ,lbs),body) when
               FStar_List.contains CompressUvars cfg.steps ->
               let uu____12027 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____12027 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____12063 =
                               let uu___184_12064 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___184_12064.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___184_12064.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____12063 in
                           let uu____12065 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____12065 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____12085 =
                                   FStar_List.map (fun uu____12089  -> Dummy)
                                     lbs1 in
                                 let uu____12090 =
                                   let uu____12093 =
                                     FStar_List.map
                                       (fun uu____12101  -> Dummy) xs1 in
                                   FStar_List.append uu____12093 env in
                                 FStar_List.append uu____12085 uu____12090 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____12113 =
                                       let uu___185_12114 = rc in
                                       let uu____12115 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___185_12114.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____12115;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___185_12114.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____12113
                                 | uu____12122 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___186_12126 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___186_12126.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___186_12126.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____12130 =
                        FStar_List.map (fun uu____12134  -> Dummy) lbs2 in
                      FStar_List.append uu____12130 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____12136 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____12136 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___187_12152 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___187_12152.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___187_12152.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____12179 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____12179
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____12198 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____12249  ->
                        match uu____12249 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____12322 =
                                let uu___188_12323 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___188_12323.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___188_12323.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____12322 in
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
               (match uu____12198 with
                | (rec_env,memos,uu____12427) ->
                    let uu____12456 =
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
                             let uu____12526 =
                               let uu____12527 =
                                 let uu____12546 =
                                   FStar_Util.mk_ref
                                     FStar_Pervasives_Native.None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____12546, false) in
                               Clos uu____12527 in
                             uu____12526 :: env1)
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
                             FStar_Syntax_Syntax.pos = uu____12602;
                             FStar_Syntax_Syntax.vars = uu____12603;_},uu____12604,uu____12605))::uu____12606
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____12613 -> false in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____12623 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____12623
                        then
                          let uu___189_12624 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___189_12624.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps =
                              (uu___189_12624.primitive_steps)
                          }
                        else
                          (let uu___190_12626 = cfg in
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___190_12626.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta];
                             primitive_steps =
                               (uu___190_12626.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____12628 =
                         let uu____12629 = FStar_Syntax_Subst.compress head1 in
                         uu____12629.FStar_Syntax_Syntax.n in
                       match uu____12628 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____12647 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____12647 with
                            | (uu____12648,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____12654 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____12662 =
                                         let uu____12663 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____12663.FStar_Syntax_Syntax.n in
                                       match uu____12662 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____12669,uu____12670))
                                           ->
                                           let uu____12679 =
                                             let uu____12680 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____12680.FStar_Syntax_Syntax.n in
                                           (match uu____12679 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____12686,msrc,uu____12688))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____12697 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____12697
                                            | uu____12698 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____12699 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____12700 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____12700 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___191_12705 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___191_12705.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___191_12705.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___191_12705.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____12706 =
                                            FStar_List.tl stack1 in
                                          let uu____12707 =
                                            let uu____12708 =
                                              let uu____12711 =
                                                let uu____12712 =
                                                  let uu____12725 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____12725) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____12712 in
                                              FStar_Syntax_Syntax.mk
                                                uu____12711 in
                                            uu____12708
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____12706
                                            uu____12707
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____12741 =
                                            let uu____12742 = is_return body in
                                            match uu____12742 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____12746;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____12747;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____12752 -> false in
                                          if uu____12741
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
                                               let uu____12776 =
                                                 let uu____12779 =
                                                   let uu____12780 =
                                                     let uu____12797 =
                                                       let uu____12800 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____12800] in
                                                     (uu____12797, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc)) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____12780 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____12779 in
                                               uu____12776
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____12816 =
                                                 let uu____12817 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____12817.FStar_Syntax_Syntax.n in
                                               match uu____12816 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____12823::uu____12824::[])
                                                   ->
                                                   let uu____12831 =
                                                     let uu____12834 =
                                                       let uu____12835 =
                                                         let uu____12842 =
                                                           let uu____12845 =
                                                             let uu____12846
                                                               =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____12846 in
                                                           let uu____12847 =
                                                             let uu____12850
                                                               =
                                                               let uu____12851
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____12851 in
                                                             [uu____12850] in
                                                           uu____12845 ::
                                                             uu____12847 in
                                                         (bind1, uu____12842) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____12835 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____12834 in
                                                   uu____12831
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____12859 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____12865 =
                                                 let uu____12868 =
                                                   let uu____12869 =
                                                     let uu____12884 =
                                                       let uu____12887 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____12888 =
                                                         let uu____12891 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____12892 =
                                                           let uu____12895 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____12896 =
                                                             let uu____12899
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____12900
                                                               =
                                                               let uu____12903
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____12904
                                                                 =
                                                                 let uu____12907
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____12907] in
                                                               uu____12903 ::
                                                                 uu____12904 in
                                                             uu____12899 ::
                                                               uu____12900 in
                                                           uu____12895 ::
                                                             uu____12896 in
                                                         uu____12891 ::
                                                           uu____12892 in
                                                       uu____12887 ::
                                                         uu____12888 in
                                                     (bind_inst, uu____12884) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____12869 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____12868 in
                                               uu____12865
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____12915 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____12915 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____12939 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____12939 with
                            | (uu____12940,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____12969 =
                                        let uu____12970 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____12970.FStar_Syntax_Syntax.n in
                                      match uu____12969 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____12976) -> t4
                                      | uu____12981 -> head2 in
                                    let uu____12982 =
                                      let uu____12983 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____12983.FStar_Syntax_Syntax.n in
                                    match uu____12982 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____12989 ->
                                        FStar_Pervasives_Native.None in
                                  let uu____12990 = maybe_extract_fv head2 in
                                  match uu____12990 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____13000 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____13000
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____13005 =
                                          maybe_extract_fv head3 in
                                        match uu____13005 with
                                        | FStar_Pervasives_Native.Some
                                            uu____13010 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____13011 ->
                                            FStar_Pervasives_Native.Some
                                              false in
                                      (head3, action_unfolded)
                                  | uu____13016 ->
                                      (head2, FStar_Pervasives_Native.None) in
                                ((let is_arg_impure uu____13031 =
                                    match uu____13031 with
                                    | (e,q) ->
                                        let uu____13038 =
                                          let uu____13039 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____13039.FStar_Syntax_Syntax.n in
                                        (match uu____13038 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____13054 -> false) in
                                  let uu____13055 =
                                    let uu____13056 =
                                      let uu____13063 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____13063 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____13056 in
                                  if uu____13055
                                  then
                                    let uu____13068 =
                                      let uu____13069 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____13069 in
                                    failwith uu____13068
                                  else ());
                                 (let uu____13071 =
                                    maybe_unfold_action head_app in
                                  match uu____13071 with
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
                                      let uu____13110 = FStar_List.tl stack1 in
                                      norm cfg env uu____13110 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____13124 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____13124 in
                           let uu____13125 = FStar_List.tl stack1 in
                           norm cfg env uu____13125 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____13246  ->
                                     match uu____13246 with
                                     | (pat,wopt,tm) ->
                                         let uu____13294 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____13294))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____13326 = FStar_List.tl stack1 in
                           norm cfg env uu____13326 tm
                       | uu____13327 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.pos = uu____13336;
                             FStar_Syntax_Syntax.vars = uu____13337;_},uu____13338,uu____13339))::uu____13340
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____13347 -> false in
                    if should_reify
                    then
                      let uu____13348 = FStar_List.tl stack1 in
                      let uu____13349 =
                        let uu____13350 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____13350 in
                      norm cfg env uu____13348 uu____13349
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____13353 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____13353
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___192_13362 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___192_13362.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___192_13362.primitive_steps)
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
                | uu____13364 ->
                    (match stack1 with
                     | uu____13365::uu____13366 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled
                              (l,r,uu____13371) ->
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
                          | uu____13396 -> norm cfg env stack1 head1)
                     | [] ->
                         let head2 = norm cfg env [] head1 in
                         let m1 =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               let uu____13410 =
                                 norm_pattern_args cfg env args in
                               FStar_Syntax_Syntax.Meta_pattern uu____13410
                           | uu____13421 -> m in
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
              let uu____13433 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____13433 with
              | (uu____13434,return_repr) ->
                  let return_inst =
                    let uu____13443 =
                      let uu____13444 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____13444.FStar_Syntax_Syntax.n in
                    match uu____13443 with
                    | FStar_Syntax_Syntax.Tm_uinst
                        (return_tm,uu____13450::[]) ->
                        let uu____13457 =
                          let uu____13460 =
                            let uu____13461 =
                              let uu____13468 =
                                let uu____13471 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____13471] in
                              (return_tm, uu____13468) in
                            FStar_Syntax_Syntax.Tm_uinst uu____13461 in
                          FStar_Syntax_Syntax.mk uu____13460 in
                        uu____13457 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____13479 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____13482 =
                    let uu____13485 =
                      let uu____13486 =
                        let uu____13501 =
                          let uu____13504 = FStar_Syntax_Syntax.as_arg t in
                          let uu____13505 =
                            let uu____13508 = FStar_Syntax_Syntax.as_arg e in
                            [uu____13508] in
                          uu____13504 :: uu____13505 in
                        (return_inst, uu____13501) in
                      FStar_Syntax_Syntax.Tm_app uu____13486 in
                    FStar_Syntax_Syntax.mk uu____13485 in
                  uu____13482 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____13517 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____13517 with
               | FStar_Pervasives_Native.None  ->
                   let uu____13520 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____13520
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____13521;
                     FStar_TypeChecker_Env.mtarget = uu____13522;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____13523;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____13534;
                     FStar_TypeChecker_Env.mtarget = uu____13535;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____13536;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____13554 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____13554)
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
                (fun uu____13610  ->
                   match uu____13610 with
                   | (a,imp) ->
                       let uu____13621 = norm cfg env [] a in
                       (uu____13621, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___193_13638 = comp1 in
            let uu____13641 =
              let uu____13642 =
                let uu____13651 = norm cfg env [] t in
                let uu____13652 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____13651, uu____13652) in
              FStar_Syntax_Syntax.Total uu____13642 in
            {
              FStar_Syntax_Syntax.n = uu____13641;
              FStar_Syntax_Syntax.pos =
                (uu___193_13638.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___193_13638.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___194_13667 = comp1 in
            let uu____13670 =
              let uu____13671 =
                let uu____13680 = norm cfg env [] t in
                let uu____13681 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____13680, uu____13681) in
              FStar_Syntax_Syntax.GTotal uu____13671 in
            {
              FStar_Syntax_Syntax.n = uu____13670;
              FStar_Syntax_Syntax.pos =
                (uu___194_13667.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___194_13667.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____13733  ->
                      match uu____13733 with
                      | (a,i) ->
                          let uu____13744 = norm cfg env [] a in
                          (uu____13744, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___147_13755  ->
                      match uu___147_13755 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____13759 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____13759
                      | f -> f)) in
            let uu___195_13763 = comp1 in
            let uu____13766 =
              let uu____13767 =
                let uu___196_13768 = ct in
                let uu____13769 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____13770 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____13773 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____13769;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___196_13768.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____13770;
                  FStar_Syntax_Syntax.effect_args = uu____13773;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____13767 in
            {
              FStar_Syntax_Syntax.n = uu____13766;
              FStar_Syntax_Syntax.pos =
                (uu___195_13763.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___195_13763.FStar_Syntax_Syntax.vars)
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
            (let uu___197_13791 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___197_13791.tcenv);
               delta_level = (uu___197_13791.delta_level);
               primitive_steps = (uu___197_13791.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____13796 = norm1 t in
          FStar_Syntax_Util.non_informative uu____13796 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____13799 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___198_13818 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.pos =
                (uu___198_13818.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___198_13818.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____13825 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____13825
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
                    let uu___199_13836 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___199_13836.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___199_13836.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___199_13836.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___200_13838 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___200_13838.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___200_13838.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___200_13838.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___200_13838.FStar_Syntax_Syntax.flags)
                    } in
              let uu___201_13839 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos =
                  (uu___201_13839.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___201_13839.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____13841 -> c
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____13844  ->
        match uu____13844 with
        | (x,imp) ->
            let uu____13847 =
              let uu___202_13848 = x in
              let uu____13849 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___202_13848.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___202_13848.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____13849
              } in
            (uu____13847, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____13855 =
          FStar_List.fold_left
            (fun uu____13873  ->
               fun b  ->
                 match uu____13873 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____13855 with | (nbs,uu____13901) -> FStar_List.rev nbs
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
            let uu____13917 =
              let uu___203_13918 = rc in
              let uu____13919 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___203_13918.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____13919;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___203_13918.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____13917
        | uu____13926 -> lopt
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
              ((let uu____13938 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____13938
                then
                  let uu____13939 = FStar_Syntax_Print.term_to_string tm in
                  let uu____13940 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2 "Normalized %s to %s\n" uu____13939
                    uu____13940
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___204_13958 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___204_13958.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____13987  ->
                    let uu____13988 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____13988);
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
              let uu____14024 =
                let uu___205_14025 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___205_14025.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___205_14025.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____14024
          | (Arg (Univ uu____14026,uu____14027,uu____14028))::uu____14029 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____14032,uu____14033))::uu____14034 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____14050),aq,r))::stack2 ->
              (log cfg
                 (fun uu____14079  ->
                    let uu____14080 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____14080);
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
                 (let uu____14090 = FStar_ST.read m in
                  match uu____14090 with
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
                  | FStar_Pervasives_Native.Some (uu____14126,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq)
                          FStar_Pervasives_Native.None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 =
                FStar_Syntax_Syntax.extend_app head1 (t, aq)
                  FStar_Pervasives_Native.None r in
              let uu____14150 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____14150
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____14160  ->
                    let uu____14161 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____14161);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____14166 =
                  log cfg
                    (fun uu____14171  ->
                       let uu____14172 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____14173 =
                         let uu____14174 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____14191  ->
                                   match uu____14191 with
                                   | (p,uu____14201,uu____14202) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____14174
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____14172 uu____14173);
                  (let whnf = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___148_14219  ->
                               match uu___148_14219 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____14220 -> false)) in
                     let steps' =
                       let uu____14224 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____14224
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___206_14228 = cfg in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___206_14228.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___206_14228.primitive_steps)
                     } in
                   let norm_or_whnf env2 t1 =
                     if whnf
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____14272 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____14295 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____14361  ->
                                   fun uu____14362  ->
                                     match (uu____14361, uu____14362) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____14465 = norm_pat env3 p1 in
                                         (match uu____14465 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____14295 with
                          | (pats1,env3) ->
                              ((let uu___207_14567 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.p =
                                    (uu___207_14567.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___208_14586 = x in
                           let uu____14587 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___208_14586.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___208_14586.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____14587
                           } in
                         ((let uu___209_14595 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.p =
                               (uu___209_14595.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___210_14600 = x in
                           let uu____14601 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___210_14600.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___210_14600.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____14601
                           } in
                         ((let uu___211_14609 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.p =
                               (uu___211_14609.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___212_14619 = x in
                           let uu____14620 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___212_14619.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___212_14619.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____14620
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___213_14629 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.p =
                               (uu___213_14629.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf -> branches
                     | uu____14633 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____14647 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____14647 with
                                 | (p,wopt,e) ->
                                     let uu____14667 = norm_pat env1 p in
                                     (match uu____14667 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Pervasives_Native.Some w
                                                ->
                                                let uu____14698 =
                                                  norm_or_whnf env2 w in
                                                FStar_Pervasives_Native.Some
                                                  uu____14698 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____14704 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____14704) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____14714) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____14719 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____14720;
                        FStar_Syntax_Syntax.fv_delta = uu____14721;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Data_ctor );_}
                      -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____14722;
                        FStar_Syntax_Syntax.fv_delta = uu____14723;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Record_ctor uu____14724);_}
                      -> true
                  | uu____14731 -> false in
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
                  let uu____14860 =
                    FStar_Syntax_Util.head_and_args scrutinee1 in
                  match uu____14860 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var uu____14909 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_wild uu____14912 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____14915 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee1.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____14934 ->
                                let uu____14935 =
                                  let uu____14936 = is_cons head1 in
                                  Prims.op_Negation uu____14936 in
                                FStar_Util.Inr uu____14935)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____14957 =
                             let uu____14958 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____14958.FStar_Syntax_Syntax.n in
                           (match uu____14957 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____14968 ->
                                let uu____14969 =
                                  let uu____14970 = is_cons head1 in
                                  Prims.op_Negation uu____14970 in
                                FStar_Util.Inr uu____14969))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____15023)::rest_a,(p1,uu____15026)::rest_p) ->
                      let uu____15070 = matches_pat t1 p1 in
                      (match uu____15070 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____15095 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____15197 = matches_pat scrutinee1 p1 in
                      (match uu____15197 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____15217  ->
                                 let uu____15218 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____15219 =
                                   let uu____15220 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____15220
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____15218 uu____15219);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____15237 =
                                        let uu____15238 =
                                          let uu____15257 =
                                            FStar_Util.mk_ref
                                              (FStar_Pervasives_Native.Some
                                                 ([], t1)) in
                                          ([], t1, uu____15257, false) in
                                        Clos uu____15238 in
                                      uu____15237 :: env2) env1 s in
                             let uu____15298 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____15298))) in
                let uu____15299 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____15299
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___149_15322  ->
                match uu___149_15322 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____15326 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____15332 -> d in
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
            let uu___214_15361 = config s e in
            {
              steps = (uu___214_15361.steps);
              tcenv = (uu___214_15361.tcenv);
              delta_level = (uu___214_15361.delta_level);
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
      fun t  -> let uu____15386 = config s e in norm_comp uu____15386 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____15395 = config [] env in norm_universe uu____15395 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let uu____15404 = config [] env in ghost_to_pure_aux uu____15404 [] c
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
        let uu____15418 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____15418 in
      let uu____15419 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____15419
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___215_15421 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___215_15421.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___215_15421.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____15424  ->
                    let uu____15425 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____15425))
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
            ((let uu____15444 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____15444);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____15457 = config [AllowUnboundUniverses] env in
          norm_comp uu____15457 [] c
        with
        | e ->
            ((let uu____15464 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____15464);
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
                   let uu____15504 =
                     let uu____15505 =
                       let uu____15512 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____15512) in
                     FStar_Syntax_Syntax.Tm_refine uu____15505 in
                   mk uu____15504 t01.FStar_Syntax_Syntax.pos
               | uu____15517 -> t2)
          | uu____15518 -> t2 in
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
        let uu____15570 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____15570 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____15599 ->
                 let uu____15606 = FStar_Syntax_Util.abs_formals e in
                 (match uu____15606 with
                  | (actuals,uu____15616,uu____15617) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____15631 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____15631 with
                         | (binders,args) ->
                             let uu____15648 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____15648
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
      | uu____15658 ->
          let uu____15659 = FStar_Syntax_Util.head_and_args t in
          (match uu____15659 with
           | (head1,args) ->
               let uu____15696 =
                 let uu____15697 = FStar_Syntax_Subst.compress head1 in
                 uu____15697.FStar_Syntax_Syntax.n in
               (match uu____15696 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____15700,thead) ->
                    let uu____15726 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____15726 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____15768 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___220_15776 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___220_15776.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___220_15776.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___220_15776.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___220_15776.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___220_15776.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___220_15776.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___220_15776.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___220_15776.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___220_15776.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___220_15776.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___220_15776.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___220_15776.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___220_15776.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___220_15776.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___220_15776.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___220_15776.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___220_15776.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___220_15776.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___220_15776.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___220_15776.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___220_15776.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___220_15776.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___220_15776.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___220_15776.FStar_TypeChecker_Env.is_native_tactic)
                                 }) t in
                            match uu____15768 with
                            | (uu____15777,ty,uu____15779) ->
                                eta_expand_with_type env t ty))
                | uu____15780 ->
                    let uu____15781 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___221_15789 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___221_15789.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___221_15789.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___221_15789.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___221_15789.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___221_15789.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___221_15789.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___221_15789.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___221_15789.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___221_15789.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___221_15789.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___221_15789.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___221_15789.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___221_15789.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___221_15789.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___221_15789.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___221_15789.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___221_15789.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___221_15789.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___221_15789.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___221_15789.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___221_15789.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___221_15789.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___221_15789.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___221_15789.FStar_TypeChecker_Env.is_native_tactic)
                         }) t in
                    (match uu____15781 with
                     | (uu____15790,ty,uu____15792) ->
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
            | (uu____15870,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____15876,FStar_Util.Inl t) ->
                let uu____15882 =
                  let uu____15885 =
                    let uu____15886 =
                      let uu____15899 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____15899) in
                    FStar_Syntax_Syntax.Tm_arrow uu____15886 in
                  FStar_Syntax_Syntax.mk uu____15885 in
                uu____15882 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____15903 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____15903 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____15930 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____15985 ->
                    let uu____15986 =
                      let uu____15995 =
                        let uu____15996 = FStar_Syntax_Subst.compress t3 in
                        uu____15996.FStar_Syntax_Syntax.n in
                      (uu____15995, tc) in
                    (match uu____15986 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____16021) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____16058) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____16097,FStar_Util.Inl uu____16098) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____16121 -> failwith "Impossible") in
              (match uu____15930 with
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
          let uu____16230 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____16230 with
          | (univ_names1,binders1,tc) ->
              let uu____16288 = FStar_Util.left tc in
              (univ_names1, binders1, uu____16288)
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
          let uu____16327 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____16327 with
          | (univ_names1,binders1,tc) ->
              let uu____16387 = FStar_Util.right tc in
              (univ_names1, binders1, uu____16387)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____16422 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____16422 with
           | (univ_names1,binders1,typ1) ->
               let uu___222_16450 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___222_16450.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___222_16450.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___222_16450.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___222_16450.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___223_16471 = s in
          let uu____16472 =
            let uu____16473 =
              let uu____16482 = FStar_List.map (elim_uvars env) sigs in
              (uu____16482, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____16473 in
          {
            FStar_Syntax_Syntax.sigel = uu____16472;
            FStar_Syntax_Syntax.sigrng =
              (uu___223_16471.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___223_16471.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___223_16471.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___223_16471.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____16499 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____16499 with
           | (univ_names1,uu____16517,typ1) ->
               let uu___224_16531 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___224_16531.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___224_16531.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___224_16531.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___224_16531.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____16537 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____16537 with
           | (univ_names1,uu____16555,typ1) ->
               let uu___225_16569 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___225_16569.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___225_16569.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___225_16569.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___225_16569.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____16603 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____16603 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____16626 =
                            let uu____16627 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____16627 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____16626 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___226_16630 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___226_16630.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___226_16630.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___227_16631 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___227_16631.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___227_16631.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___227_16631.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___227_16631.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___228_16643 = s in
          let uu____16644 =
            let uu____16645 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____16645 in
          {
            FStar_Syntax_Syntax.sigel = uu____16644;
            FStar_Syntax_Syntax.sigrng =
              (uu___228_16643.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___228_16643.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___228_16643.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___228_16643.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____16649 = elim_uvars_aux_t env us [] t in
          (match uu____16649 with
           | (us1,uu____16667,t1) ->
               let uu___229_16681 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___229_16681.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___229_16681.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___229_16681.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___229_16681.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____16682 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____16684 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____16684 with
           | (univs1,binders,signature) ->
               let uu____16712 =
                 let uu____16721 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____16721 with
                 | (univs_opening,univs2) ->
                     let uu____16748 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____16748) in
               (match uu____16712 with
                | (univs_opening,univs_closing) ->
                    let uu____16765 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____16771 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____16772 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____16771, uu____16772) in
                    (match uu____16765 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____16794 =
                           match uu____16794 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____16812 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____16812 with
                                | (us1,t1) ->
                                    let uu____16823 =
                                      let uu____16828 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____16835 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____16828, uu____16835) in
                                    (match uu____16823 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____16848 =
                                           let uu____16853 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____16862 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____16853, uu____16862) in
                                         (match uu____16848 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____16878 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____16878 in
                                              let uu____16879 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____16879 with
                                               | (uu____16900,uu____16901,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____16916 =
                                                       let uu____16917 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____16917 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____16916 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____16922 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____16922 with
                           | (uu____16935,uu____16936,t1) -> t1 in
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
                             | uu____16996 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____17013 =
                               let uu____17014 =
                                 FStar_Syntax_Subst.compress body in
                               uu____17014.FStar_Syntax_Syntax.n in
                             match uu____17013 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____17073 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____17102 =
                               let uu____17103 =
                                 FStar_Syntax_Subst.compress t in
                               uu____17103.FStar_Syntax_Syntax.n in
                             match uu____17102 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____17124) ->
                                 let uu____17145 = destruct_action_body body in
                                 (match uu____17145 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____17190 ->
                                 let uu____17191 = destruct_action_body t in
                                 (match uu____17191 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____17240 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____17240 with
                           | (action_univs,t) ->
                               let uu____17249 = destruct_action_typ_templ t in
                               (match uu____17249 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___230_17290 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___230_17290.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___230_17290.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___231_17292 = ed in
                           let uu____17293 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____17294 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____17295 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____17296 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____17297 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____17298 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____17299 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____17300 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____17301 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____17302 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____17303 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____17304 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____17305 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____17306 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___231_17292.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___231_17292.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____17293;
                             FStar_Syntax_Syntax.bind_wp = uu____17294;
                             FStar_Syntax_Syntax.if_then_else = uu____17295;
                             FStar_Syntax_Syntax.ite_wp = uu____17296;
                             FStar_Syntax_Syntax.stronger = uu____17297;
                             FStar_Syntax_Syntax.close_wp = uu____17298;
                             FStar_Syntax_Syntax.assert_p = uu____17299;
                             FStar_Syntax_Syntax.assume_p = uu____17300;
                             FStar_Syntax_Syntax.null_wp = uu____17301;
                             FStar_Syntax_Syntax.trivial = uu____17302;
                             FStar_Syntax_Syntax.repr = uu____17303;
                             FStar_Syntax_Syntax.return_repr = uu____17304;
                             FStar_Syntax_Syntax.bind_repr = uu____17305;
                             FStar_Syntax_Syntax.actions = uu____17306
                           } in
                         let uu___232_17309 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___232_17309.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___232_17309.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___232_17309.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___232_17309.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___150_17326 =
            match uu___150_17326 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____17353 = elim_uvars_aux_t env us [] t in
                (match uu____17353 with
                 | (us1,uu____17377,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___233_17396 = sub_eff in
            let uu____17397 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____17400 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___233_17396.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___233_17396.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____17397;
              FStar_Syntax_Syntax.lift = uu____17400
            } in
          let uu___234_17403 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___234_17403.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___234_17403.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___234_17403.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___234_17403.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____17413 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____17413 with
           | (univ_names1,binders1,comp1) ->
               let uu___235_17447 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___235_17447.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___235_17447.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___235_17447.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___235_17447.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____17458 -> s