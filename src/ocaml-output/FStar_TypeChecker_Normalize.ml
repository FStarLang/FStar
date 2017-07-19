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
let mk t r = FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r
let set_memo r t =
  let uu____1024 = FStar_ST.read r in
  match uu____1024 with
  | FStar_Pervasives_Native.Some uu____1031 ->
      failwith "Unexpected set_memo: thunk already evaluated"
  | FStar_Pervasives_Native.None  ->
      FStar_ST.write r (FStar_Pervasives_Native.Some t)
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____1044 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____1044 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___139_1052  ->
    match uu___139_1052 with
    | Arg (c,uu____1054,uu____1055) ->
        let uu____1056 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____1056
    | MemoLazy uu____1057 -> "MemoLazy"
    | Abs (uu____1064,bs,uu____1066,uu____1067,uu____1068) ->
        let uu____1073 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____1073
    | UnivArgs uu____1078 -> "UnivArgs"
    | Match uu____1085 -> "Match"
    | App (t,uu____1093,uu____1094) ->
        let uu____1095 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____1095
    | Meta (m,uu____1097) -> "Meta"
    | Let uu____1098 -> "Let"
    | Steps (uu____1107,uu____1108,uu____1109) -> "Steps"
    | Debug t ->
        let uu____1119 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____1119
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____1128 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____1128 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1146 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____1146 then f () else ()
let is_empty uu___140_1158 =
  match uu___140_1158 with | [] -> true | uu____1161 -> false
let lookup_bvar env x =
  try FStar_List.nth env x.FStar_Syntax_Syntax.index
  with
  | uu____1189 ->
      let uu____1190 =
        let uu____1191 = FStar_Syntax_Print.db_to_string x in
        FStar_Util.format1 "Failed to find %s\n" uu____1191 in
      failwith uu____1190
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
          let uu____1236 =
            FStar_List.fold_left
              (fun uu____1262  ->
                 fun u1  ->
                   match uu____1262 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____1287 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____1287 with
                        | (k_u,n1) ->
                            let uu____1302 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____1302
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____1236 with
          | (uu____1320,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____1345 = FStar_List.nth env x in
                 match uu____1345 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____1349 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____1358 ->
                   let uu____1359 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____1359
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____1365 when
              FStar_All.pipe_right cfg.steps
                (FStar_List.contains CheckNoUvars)
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1374 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1383 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1390 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____1390 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____1407 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____1407 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____1415 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____1423 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____1423 with
                                  | (uu____1428,m) -> n1 <= m)) in
                        if uu____1415 then rest1 else us1
                    | uu____1433 -> us1)
               | uu____1438 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1442 = aux u3 in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____1442 in
        let uu____1445 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____1445
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1447 = aux u in
           match uu____1447 with
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
          (fun uu____1579  ->
             let uu____1580 = FStar_Syntax_Print.tag_of_term t in
             let uu____1581 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1580
               uu____1581);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1582 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1586 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  ->
                  (FStar_ST.write t1.FStar_Syntax_Syntax.tk
                     FStar_Pervasives_Native.None;
                   t1)
              | FStar_Syntax_Syntax.Tm_constant uu____1618 ->
                  (FStar_ST.write t1.FStar_Syntax_Syntax.tk
                     FStar_Pervasives_Native.None;
                   t1)
              | FStar_Syntax_Syntax.Tm_name uu____1622 ->
                  (FStar_ST.write t1.FStar_Syntax_Syntax.tk
                     FStar_Pervasives_Native.None;
                   t1)
              | FStar_Syntax_Syntax.Tm_fvar uu____1626 ->
                  (FStar_ST.write t1.FStar_Syntax_Syntax.tk
                     FStar_Pervasives_Native.None;
                   t1)
              | FStar_Syntax_Syntax.Tm_uvar uu____1630 ->
                  let uu____1651 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains CheckNoUvars) in
                  if uu____1651
                  then
                    let uu____1652 =
                      let uu____1653 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos in
                      let uu____1654 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____1653 uu____1654 in
                    failwith uu____1652
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____1657 =
                    let uu____1658 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____1658 in
                  mk uu____1657 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____1669 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____1669
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____1671 = lookup_bvar env x in
                  (match uu____1671 with
                   | Univ uu____1672 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____1676) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____1784 = closures_as_binders_delayed cfg env bs in
                  (match uu____1784 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____1820 =
                         let uu____1821 =
                           let uu____1840 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____1840) in
                         FStar_Syntax_Syntax.Tm_abs uu____1821 in
                       mk uu____1820 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____1877 = closures_as_binders_delayed cfg env bs in
                  (match uu____1877 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____1933 =
                    let uu____1946 =
                      let uu____1953 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____1953] in
                    closures_as_binders_delayed cfg env uu____1946 in
                  (match uu____1933 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____1977 =
                         let uu____1978 =
                           let uu____1987 =
                             let uu____1988 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____1988
                               FStar_Pervasives_Native.fst in
                           (uu____1987, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____1978 in
                       mk uu____1977 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____2117 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____2117
                    | FStar_Util.Inr c ->
                        let uu____2143 = close_comp cfg env c in
                        FStar_Util.Inr uu____2143 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____2171 =
                    let uu____2172 =
                      let uu____2207 = closure_as_term_delayed cfg env t11 in
                      (uu____2207, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____2172 in
                  mk uu____2171 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____2280 =
                    let uu____2281 =
                      let uu____2290 = closure_as_term_delayed cfg env t' in
                      let uu____2295 =
                        let uu____2296 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____2296 in
                      (uu____2290, uu____2295) in
                    FStar_Syntax_Syntax.Tm_meta uu____2281 in
                  mk uu____2280 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____2376 =
                    let uu____2377 =
                      let uu____2386 = closure_as_term_delayed cfg env t' in
                      let uu____2391 =
                        let uu____2392 =
                          let uu____2401 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____2401) in
                        FStar_Syntax_Syntax.Meta_monadic uu____2392 in
                      (uu____2386, uu____2391) in
                    FStar_Syntax_Syntax.Tm_meta uu____2377 in
                  mk uu____2376 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____2434 =
                    let uu____2435 =
                      let uu____2444 = closure_as_term_delayed cfg env t' in
                      let uu____2449 =
                        let uu____2450 =
                          let uu____2461 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____2461) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____2450 in
                      (uu____2444, uu____2449) in
                    FStar_Syntax_Syntax.Tm_meta uu____2435 in
                  mk uu____2434 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____2484 =
                    let uu____2485 =
                      let uu____2494 = closure_as_term_delayed cfg env t' in
                      (uu____2494, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____2485 in
                  mk uu____2484 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____2532  -> Dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let uu____2541 =
                    let uu____2554 = FStar_Syntax_Syntax.is_top_level [lb] in
                    if uu____2554
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       let uu____2577 =
                         closure_as_term cfg (Dummy :: env0) body in
                       ((FStar_Util.Inl
                           (let uu___155_2583 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___155_2583.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___155_2583.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____2577)) in
                  (match uu____2541 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___156_2603 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___156_2603.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___156_2603.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         } in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____2616,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____2655  -> fun env2  -> Dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____2662 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2662
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____2670  -> fun env2  -> Dummy :: env2) lbs
                          env_univs in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let nm =
                      let uu____2680 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2680
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         FStar_All.pipe_right
                           (let uu___157_2692 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___157_2692.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___157_2692.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41)) in
                    let uu___158_2693 = lb in
                    let uu____2694 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___158_2693.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___158_2693.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____2694
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____2714  -> fun env1  -> Dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____2805 =
                    match uu____2805 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____2870 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____2893 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____2959  ->
                                        fun uu____2960  ->
                                          match (uu____2959, uu____2960) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____3063 =
                                                norm_pat env3 p1 in
                                              (match uu____3063 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____2893 with
                               | (pats1,env3) ->
                                   ((let uu___159_3165 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___159_3165.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___160_3184 = x in
                                let uu____3185 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___160_3184.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___160_3184.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3185
                                } in
                              ((let uu___161_3195 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___161_3195.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___162_3200 = x in
                                let uu____3201 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___162_3200.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___162_3200.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3201
                                } in
                              ((let uu___163_3211 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___163_3211.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___164_3225 = x in
                                let uu____3226 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___164_3225.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___164_3225.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3226
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___165_3237 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___165_3237.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____3240 = norm_pat env1 pat in
                        (match uu____3240 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3275 =
                                     closure_as_term cfg env2 w in
                                   FStar_Pervasives_Native.Some uu____3275 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____3281 =
                    let uu____3282 =
                      let uu____3311 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____3311) in
                    FStar_Syntax_Syntax.Tm_match uu____3282 in
                  mk uu____3281 t1.FStar_Syntax_Syntax.pos))
and closure_as_term_delayed:
  cfg ->
    closure Prims.list ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun t  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains CompressUvars cfg.steps)
            -> t
        | uu____3401 -> closure_as_term cfg env t
and closures_as_args_delayed:
  cfg ->
    closure Prims.list ->
      ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
         FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
           FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
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
        | uu____3429 ->
            FStar_List.map
              (fun uu____3452  ->
                 match uu____3452 with
                 | (x,imp) ->
                     let uu____3479 = closure_as_term_delayed cfg env x in
                     (uu____3479, imp)) args
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
        let uu____3499 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____3554  ->
                  fun uu____3555  ->
                    match (uu____3554, uu____3555) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___166_3637 = b in
                          let uu____3638 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___166_3637.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___166_3637.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____3638
                          } in
                        let env2 = Dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____3499 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
and close_comp:
  cfg ->
    closure Prims.list ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun cfg  ->
    fun env  ->
      fun c  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains CompressUvars cfg.steps)
            -> c
        | uu____3725 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____3746 = closure_as_term_delayed cfg env t in
                 let uu____3747 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____3746 uu____3747
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____3764 = closure_as_term_delayed cfg env t in
                 let uu____3765 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____3764 uu____3765
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
                        (fun uu___141_3795  ->
                           match uu___141_3795 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____3801 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____3801
                           | f -> f)) in
                 let uu____3807 =
                   let uu___167_3808 = c1 in
                   let uu____3809 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____3809;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___167_3808.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____3807)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags  ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___142_3819  ->
            match uu___142_3819 with
            | FStar_Syntax_Syntax.DECREASES uu____3820 -> false
            | uu____3825 -> true))
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
                   (fun uu___143_3845  ->
                      match uu___143_3845 with
                      | FStar_Syntax_Syntax.DECREASES uu____3846 -> false
                      | uu____3851 -> true)) in
            let rc1 =
              let uu___168_3853 = rc in
              let uu____3854 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___168_3853.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____3854;
                FStar_Syntax_Syntax.residual_flags = flags
              } in
            FStar_Pervasives_Native.Some rc1
        | uu____3865 -> lopt
let built_in_primitive_steps: primitive_step Prims.list =
  let const_as_tm c p = mk (FStar_Syntax_Syntax.Tm_constant c) p in
  let int_as_const p i =
    let uu____3888 =
      let uu____3889 =
        let uu____3900 = FStar_Util.string_of_int i in
        (uu____3900, FStar_Pervasives_Native.None) in
      FStar_Const.Const_int uu____3889 in
    const_as_tm uu____3888 p in
  let bool_as_const p b = const_as_tm (FStar_Const.Const_bool b) p in
  let string_as_const p b =
    const_as_tm
      (FStar_Const.Const_string ((FStar_Util.bytes_of_string b), p)) p in
  let arg_as_int uu____3936 =
    match uu____3936 with
    | (a,uu____3944) ->
        let uu____3947 =
          let uu____3948 = FStar_Syntax_Subst.compress a in
          uu____3948.FStar_Syntax_Syntax.n in
        (match uu____3947 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (i,FStar_Pervasives_Native.None )) ->
             let uu____3966 = FStar_Util.int_of_string i in
             FStar_Pervasives_Native.Some uu____3966
         | uu____3967 -> FStar_Pervasives_Native.None) in
  let arg_as_bounded_int uu____3981 =
    match uu____3981 with
    | (a,uu____3993) ->
        let uu____4000 =
          let uu____4001 = FStar_Syntax_Subst.compress a in
          uu____4001.FStar_Syntax_Syntax.n in
        (match uu____4000 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.tk = uu____4013;
                FStar_Syntax_Syntax.pos = uu____4014;
                FStar_Syntax_Syntax.vars = uu____4015;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.tk
                                                              = uu____4017;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____4018;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____4019;_},uu____4020)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____4073 =
               let uu____4078 = FStar_Util.int_of_string i in
               (fv1, uu____4078) in
             FStar_Pervasives_Native.Some uu____4073
         | uu____4083 -> FStar_Pervasives_Native.None) in
  let arg_as_bool uu____4097 =
    match uu____4097 with
    | (a,uu____4105) ->
        let uu____4108 =
          let uu____4109 = FStar_Syntax_Subst.compress a in
          uu____4109.FStar_Syntax_Syntax.n in
        (match uu____4108 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
             FStar_Pervasives_Native.Some b
         | uu____4117 -> FStar_Pervasives_Native.None) in
  let arg_as_char uu____4127 =
    match uu____4127 with
    | (a,uu____4135) ->
        let uu____4138 =
          let uu____4139 = FStar_Syntax_Subst.compress a in
          uu____4139.FStar_Syntax_Syntax.n in
        (match uu____4138 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
             FStar_Pervasives_Native.Some c
         | uu____4147 -> FStar_Pervasives_Native.None) in
  let arg_as_string uu____4157 =
    match uu____4157 with
    | (a,uu____4165) ->
        let uu____4168 =
          let uu____4169 = FStar_Syntax_Subst.compress a in
          uu____4169.FStar_Syntax_Syntax.n in
        (match uu____4168 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (bytes,uu____4177)) ->
             FStar_Pervasives_Native.Some (FStar_Util.string_of_bytes bytes)
         | uu____4182 -> FStar_Pervasives_Native.None) in
  let arg_as_list f uu____4208 =
    match uu____4208 with
    | (a,uu____4222) ->
        let rec sequence l =
          match l with
          | [] -> FStar_Pervasives_Native.Some []
          | (FStar_Pervasives_Native.None )::uu____4251 ->
              FStar_Pervasives_Native.None
          | (FStar_Pervasives_Native.Some x)::xs ->
              let uu____4268 = sequence xs in
              (match uu____4268 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some xs' ->
                   FStar_Pervasives_Native.Some (x :: xs')) in
        let uu____4288 = FStar_Syntax_Util.list_elements a in
        (match uu____4288 with
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some elts ->
             let uu____4306 =
               FStar_List.map
                 (fun x  ->
                    let uu____4316 = FStar_Syntax_Syntax.as_arg x in
                    f uu____4316) elts in
             sequence uu____4306) in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4354 = f a in FStar_Pervasives_Native.Some uu____4354
    | uu____4355 -> FStar_Pervasives_Native.None in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4405 = f a0 a1 in FStar_Pervasives_Native.Some uu____4405
    | uu____4406 -> FStar_Pervasives_Native.None in
  let unary_op as_a f r args =
    let uu____4455 = FStar_List.map as_a args in lift_unary (f r) uu____4455 in
  let binary_op as_a f r args =
    let uu____4511 = FStar_List.map as_a args in lift_binary (f r) uu____4511 in
  let as_primitive_step uu____4535 =
    match uu____4535 with
    | (l,arity,f) ->
        { name = l; arity; strong_reduction_ok = true; interpretation = f } in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  -> fun x  -> let uu____4583 = f x in int_as_const r uu____4583) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  -> let uu____4611 = f x y in int_as_const r uu____4611) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  -> fun x  -> let uu____4632 = f x in bool_as_const r uu____4632) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  -> let uu____4660 = f x y in bool_as_const r uu____4660) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  -> let uu____4688 = f x y in string_as_const r uu____4688) in
  let list_of_string' rng s =
    let name l =
      let uu____4704 =
        let uu____4705 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____4705 in
      mk uu____4704 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____4719 =
      let uu____4722 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____4722 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____4719 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in int_as_const rng r in
  let string_concat' rng args =
    match args with
    | a1::a2::[] ->
        let uu____4799 = arg_as_string a1 in
        (match uu____4799 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4805 = arg_as_list arg_as_string a2 in
             (match uu____4805 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____4818 = string_as_const rng r in
                  FStar_Pervasives_Native.Some uu____4818
              | uu____4819 -> FStar_Pervasives_Native.None)
         | uu____4824 -> FStar_Pervasives_Native.None)
    | uu____4827 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____4841 = FStar_Util.string_of_int i in
    string_as_const rng uu____4841 in
  let string_of_bool1 rng b =
    string_as_const rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____4857 = FStar_Util.string_of_int i in
    string_as_const rng uu____4857 in
  let string_of_bool2 rng b =
    string_as_const rng (if b then "true" else "false") in
  let decidable_eq neg rng args =
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) rng in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) rng in
    match args with
    | (_typ,uu____4893)::(a1,uu____4895)::(a2,uu____4897)::[] ->
        let uu____4954 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4954 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____4975 -> FStar_Pervasives_Native.None)
    | uu____4976 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____4994 =
      let uu____5009 =
        let uu____5024 =
          let uu____5039 =
            let uu____5054 =
              let uu____5069 =
                let uu____5084 =
                  let uu____5099 =
                    let uu____5114 =
                      let uu____5129 =
                        let uu____5144 =
                          let uu____5159 =
                            let uu____5174 =
                              let uu____5189 =
                                let uu____5204 =
                                  let uu____5219 =
                                    let uu____5234 =
                                      let uu____5249 =
                                        let uu____5264 =
                                          let uu____5279 =
                                            let uu____5294 =
                                              let uu____5307 =
                                                FStar_Parser_Const.p2l
                                                  ["FStar";
                                                  "String";
                                                  "list_of_string"] in
                                              (uu____5307,
                                                (Prims.parse_int "1"),
                                                (unary_op arg_as_string
                                                   list_of_string')) in
                                            let uu____5314 =
                                              let uu____5329 =
                                                let uu____5342 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "string_of_list"] in
                                                (uu____5342,
                                                  (Prims.parse_int "1"),
                                                  (unary_op
                                                     (arg_as_list arg_as_char)
                                                     string_of_list')) in
                                              let uu____5351 =
                                                let uu____5366 =
                                                  let uu____5385 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "concat"] in
                                                  (uu____5385,
                                                    (Prims.parse_int "2"),
                                                    string_concat') in
                                                [uu____5366] in
                                              uu____5329 :: uu____5351 in
                                            uu____5294 :: uu____5314 in
                                          (FStar_Parser_Const.op_notEq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq true)) ::
                                            uu____5279 in
                                        (FStar_Parser_Const.op_Eq,
                                          (Prims.parse_int "3"),
                                          (decidable_eq false)) :: uu____5264 in
                                      (FStar_Parser_Const.string_compare,
                                        (Prims.parse_int "2"),
                                        (binary_op arg_as_string
                                           string_compare'))
                                        :: uu____5249 in
                                    (FStar_Parser_Const.string_of_bool_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_bool string_of_bool2))
                                      :: uu____5234 in
                                  (FStar_Parser_Const.string_of_int_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_int string_of_int2)) ::
                                    uu____5219 in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____5204 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5189 in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____5174 in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____5159 in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____5144 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____5129 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
                      :: uu____5114 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____5099 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____5084 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____5069 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____5054 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____5039 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____5024 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____5009 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____4994 in
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
      let uu____5936 =
        let uu____5937 =
          let uu____5938 = FStar_Syntax_Syntax.as_arg c in [uu____5938] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____5937 in
      uu____5936 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____5973 =
              let uu____5986 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____5986, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____6005  ->
                        fun uu____6006  ->
                          match (uu____6005, uu____6006) with
                          | ((int_to_t1,x),(uu____6025,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____6035 =
              let uu____6050 =
                let uu____6063 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____6063, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____6082  ->
                          fun uu____6083  ->
                            match (uu____6082, uu____6083) with
                            | ((int_to_t1,x),(uu____6102,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____6112 =
                let uu____6127 =
                  let uu____6140 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____6140, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____6159  ->
                            fun uu____6160  ->
                              match (uu____6159, uu____6160) with
                              | ((int_to_t1,x),(uu____6179,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____6127] in
              uu____6050 :: uu____6112 in
            uu____5973 :: uu____6035)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop r args =
    match args with
    | (_typ,uu____6275)::(a1,uu____6277)::(a2,uu____6279)::[] ->
        let uu____6336 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6336 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___169_6344 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___169_6344.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___169_6344.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___169_6344.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___170_6350 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___170_6350.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___170_6350.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___170_6350.FStar_Syntax_Syntax.vars)
                })
         | uu____6351 -> FStar_Pervasives_Native.None)
    | (_typ,uu____6353)::uu____6354::(a1,uu____6356)::(a2,uu____6358)::[] ->
        let uu____6431 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6431 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___169_6439 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___169_6439.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___169_6439.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___169_6439.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___170_6445 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___170_6445.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___170_6445.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___170_6445.FStar_Syntax_Syntax.vars)
                })
         | uu____6446 -> FStar_Pervasives_Native.None)
    | uu____6447 -> failwith "Unexpected number of arguments" in
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
      let uu____6460 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops cfg.steps) in
      if uu____6460
      then tm
      else
        (let uu____6462 = FStar_Syntax_Util.head_and_args tm in
         match uu____6462 with
         | (head1,args) ->
             let uu____6511 =
               let uu____6512 = FStar_Syntax_Util.un_uinst head1 in
               uu____6512.FStar_Syntax_Syntax.n in
             (match uu____6511 with
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____6518 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps in
                  (match uu____6518 with
                   | FStar_Pervasives_Native.None  -> tm
                   | FStar_Pervasives_Native.Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then tm
                       else
                         (let uu____6533 =
                            prim_step.interpretation
                              head1.FStar_Syntax_Syntax.pos args in
                          match uu____6533 with
                          | FStar_Pervasives_Native.None  -> tm
                          | FStar_Pervasives_Native.Some reduced -> reduced))
              | uu____6537 -> tm))
let reduce_equality:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___171_6548 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___171_6548.tcenv);
           delta_level = (uu___171_6548.delta_level);
           primitive_steps = equality_ops
         }) tm
let maybe_simplify:
  cfg ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      let steps = cfg.steps in
      let w t =
        let uu___172_6582 = t in
        {
          FStar_Syntax_Syntax.n = (uu___172_6582.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___172_6582.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___172_6582.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid ->
            FStar_Pervasives_Native.Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid ->
            FStar_Pervasives_Native.Some false
        | uu____6605 -> FStar_Pervasives_Native.None in
      let simplify arg = ((simp_t (FStar_Pervasives_Native.fst arg)), arg) in
      let tm1 = reduce_primops cfg tm in
      let uu____6655 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps) in
      if uu____6655
      then tm1
      else
        (match tm1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.tk = uu____6658;
                     FStar_Syntax_Syntax.pos = uu____6659;
                     FStar_Syntax_Syntax.vars = uu____6660;_},uu____6661);
                FStar_Syntax_Syntax.tk = uu____6662;
                FStar_Syntax_Syntax.pos = uu____6663;
                FStar_Syntax_Syntax.vars = uu____6664;_},args)
             ->
             let uu____6702 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
             if uu____6702
             then
               let uu____6703 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____6703 with
                | (FStar_Pervasives_Native.Some (true ),uu____6768)::
                    (uu____6769,(arg,uu____6771))::[] -> arg
                | (uu____6852,(arg,uu____6854))::(FStar_Pervasives_Native.Some
                                                  (true ),uu____6855)::[]
                    -> arg
                | (FStar_Pervasives_Native.Some (false ),uu____6936)::uu____6937::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____7012::(FStar_Pervasives_Native.Some (false
                               ),uu____7013)::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____7088 -> tm1)
             else
               (let uu____7106 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
                if uu____7106
                then
                  let uu____7107 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____7107 with
                  | (FStar_Pervasives_Native.Some (true ),uu____7172)::uu____7173::[]
                      -> w FStar_Syntax_Util.t_true
                  | uu____7248::(FStar_Pervasives_Native.Some (true
                                 ),uu____7249)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____7324)::
                      (uu____7325,(arg,uu____7327))::[] -> arg
                  | (uu____7408,(arg,uu____7410))::(FStar_Pervasives_Native.Some
                                                    (false ),uu____7411)::[]
                      -> arg
                  | uu____7492 -> tm1
                else
                  (let uu____7510 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.imp_lid in
                   if uu____7510
                   then
                     let uu____7511 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____7511 with
                     | uu____7576::(FStar_Pervasives_Native.Some (true
                                    ),uu____7577)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____7652)::uu____7653::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____7728)::
                         (uu____7729,(arg,uu____7731))::[] -> arg
                     | (uu____7812,(p,uu____7814))::(uu____7815,(q,uu____7817))::[]
                         ->
                         let uu____7900 = FStar_Syntax_Util.term_eq p q in
                         (if uu____7900
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____7902 -> tm1
                   else
                     (let uu____7920 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____7920
                      then
                        let uu____7921 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____7921 with
                        | (FStar_Pervasives_Native.Some (true ),uu____7986)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____8033)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____8080 -> tm1
                      else
                        (let uu____8098 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____8098
                         then
                           match args with
                           | (t,uu____8100)::[] ->
                               let uu____8125 =
                                 let uu____8126 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____8126.FStar_Syntax_Syntax.n in
                               (match uu____8125 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____8131::[],body,uu____8133) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____8164 -> tm1)
                                | uu____8167 -> tm1)
                           | (uu____8168,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____8169))::
                               (t,uu____8171)::[] ->
                               let uu____8224 =
                                 let uu____8225 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____8225.FStar_Syntax_Syntax.n in
                               (match uu____8224 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____8230::[],body,uu____8232) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____8263 -> tm1)
                                | uu____8266 -> tm1)
                           | uu____8267 -> tm1
                         else
                           (let uu____8279 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____8279
                            then
                              match args with
                              | (t,uu____8281)::[] ->
                                  let uu____8306 =
                                    let uu____8307 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____8307.FStar_Syntax_Syntax.n in
                                  (match uu____8306 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____8312::[],body,uu____8314) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____8345 -> tm1)
                                   | uu____8348 -> tm1)
                              | (uu____8349,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____8350))::
                                  (t,uu____8352)::[] ->
                                  let uu____8405 =
                                    let uu____8406 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____8406.FStar_Syntax_Syntax.n in
                                  (match uu____8405 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____8411::[],body,uu____8413) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____8444 -> tm1)
                                   | uu____8447 -> tm1)
                              | uu____8448 -> tm1
                            else reduce_equality cfg tm1)))))
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                FStar_Syntax_Syntax.tk = uu____8461;
                FStar_Syntax_Syntax.pos = uu____8462;
                FStar_Syntax_Syntax.vars = uu____8463;_},args)
             ->
             let uu____8493 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
             if uu____8493
             then
               let uu____8494 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____8494 with
                | (FStar_Pervasives_Native.Some (true ),uu____8559)::
                    (uu____8560,(arg,uu____8562))::[] -> arg
                | (uu____8643,(arg,uu____8645))::(FStar_Pervasives_Native.Some
                                                  (true ),uu____8646)::[]
                    -> arg
                | (FStar_Pervasives_Native.Some (false ),uu____8727)::uu____8728::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____8803::(FStar_Pervasives_Native.Some (false
                               ),uu____8804)::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____8879 -> tm1)
             else
               (let uu____8897 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
                if uu____8897
                then
                  let uu____8898 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____8898 with
                  | (FStar_Pervasives_Native.Some (true ),uu____8963)::uu____8964::[]
                      -> w FStar_Syntax_Util.t_true
                  | uu____9039::(FStar_Pervasives_Native.Some (true
                                 ),uu____9040)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____9115)::
                      (uu____9116,(arg,uu____9118))::[] -> arg
                  | (uu____9199,(arg,uu____9201))::(FStar_Pervasives_Native.Some
                                                    (false ),uu____9202)::[]
                      -> arg
                  | uu____9283 -> tm1
                else
                  (let uu____9301 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.imp_lid in
                   if uu____9301
                   then
                     let uu____9302 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____9302 with
                     | uu____9367::(FStar_Pervasives_Native.Some (true
                                    ),uu____9368)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____9443)::uu____9444::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____9519)::
                         (uu____9520,(arg,uu____9522))::[] -> arg
                     | (uu____9603,(p,uu____9605))::(uu____9606,(q,uu____9608))::[]
                         ->
                         let uu____9691 = FStar_Syntax_Util.term_eq p q in
                         (if uu____9691
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____9693 -> tm1
                   else
                     (let uu____9711 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____9711
                      then
                        let uu____9712 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____9712 with
                        | (FStar_Pervasives_Native.Some (true ),uu____9777)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____9824)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____9871 -> tm1
                      else
                        (let uu____9889 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____9889
                         then
                           match args with
                           | (t,uu____9891)::[] ->
                               let uu____9916 =
                                 let uu____9917 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____9917.FStar_Syntax_Syntax.n in
                               (match uu____9916 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____9922::[],body,uu____9924) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____9955 -> tm1)
                                | uu____9958 -> tm1)
                           | (uu____9959,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____9960))::
                               (t,uu____9962)::[] ->
                               let uu____10015 =
                                 let uu____10016 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____10016.FStar_Syntax_Syntax.n in
                               (match uu____10015 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____10021::[],body,uu____10023) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____10054 -> tm1)
                                | uu____10057 -> tm1)
                           | uu____10058 -> tm1
                         else
                           (let uu____10070 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____10070
                            then
                              match args with
                              | (t,uu____10072)::[] ->
                                  let uu____10097 =
                                    let uu____10098 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____10098.FStar_Syntax_Syntax.n in
                                  (match uu____10097 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____10103::[],body,uu____10105) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____10136 -> tm1)
                                   | uu____10139 -> tm1)
                              | (uu____10140,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____10141))::
                                  (t,uu____10143)::[] ->
                                  let uu____10196 =
                                    let uu____10197 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____10197.FStar_Syntax_Syntax.n in
                                  (match uu____10196 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____10202::[],body,uu____10204) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____10235 -> tm1)
                                   | uu____10238 -> tm1)
                              | uu____10239 -> tm1
                            else reduce_equality cfg tm1)))))
         | uu____10251 -> tm1)
let is_norm_request hd1 args =
  let uu____10271 =
    let uu____10278 =
      let uu____10279 = FStar_Syntax_Util.un_uinst hd1 in
      uu____10279.FStar_Syntax_Syntax.n in
    (uu____10278, args) in
  match uu____10271 with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10287::uu____10288::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10292::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
  | uu____10295 -> false
let get_norm_request args =
  match args with
  | uu____10326::(tm,uu____10328)::[] -> tm
  | (tm,uu____10346)::[] -> tm
  | uu____10355 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___144_10367  ->
    match uu___144_10367 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.tk = uu____10370;
           FStar_Syntax_Syntax.pos = uu____10371;
           FStar_Syntax_Syntax.vars = uu____10372;_},uu____10373,uu____10374))::uu____10375
        -> true
    | uu____10386 -> false
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
            (fun uu____10529  ->
               let uu____10530 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____10531 = FStar_Syntax_Print.term_to_string t1 in
               let uu____10532 =
                 let uu____10533 =
                   let uu____10536 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____10536 in
                 stack_to_string uu____10533 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____10530
                 uu____10531 uu____10532);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____10559 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____10588 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____10609 =
                 let uu____10610 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____10611 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____10610 uu____10611 in
               failwith uu____10609
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (FStar_ST.write t1.FStar_Syntax_Syntax.tk
                  FStar_Pervasives_Native.None;
                rebuild cfg env stack1 t1)
           | FStar_Syntax_Syntax.Tm_uvar uu____10615 ->
               (FStar_ST.write t1.FStar_Syntax_Syntax.tk
                  FStar_Pervasives_Native.None;
                rebuild cfg env stack1 t1)
           | FStar_Syntax_Syntax.Tm_constant uu____10639 ->
               (FStar_ST.write t1.FStar_Syntax_Syntax.tk
                  FStar_Pervasives_Native.None;
                rebuild cfg env stack1 t1)
           | FStar_Syntax_Syntax.Tm_name uu____10643 ->
               (FStar_ST.write t1.FStar_Syntax_Syntax.tk
                  FStar_Pervasives_Native.None;
                rebuild cfg env stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10647;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____10648;_}
               ->
               (FStar_ST.write t1.FStar_Syntax_Syntax.tk
                  FStar_Pervasives_Native.None;
                rebuild cfg env stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10654;
                 FStar_Syntax_Syntax.fv_delta = uu____10655;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               ->
               (FStar_ST.write t1.FStar_Syntax_Syntax.tk
                  FStar_Pervasives_Native.None;
                rebuild cfg env stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10659;
                 FStar_Syntax_Syntax.fv_delta = uu____10660;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____10661);_}
               ->
               (FStar_ST.write t1.FStar_Syntax_Syntax.tk
                  FStar_Pervasives_Native.None;
                rebuild cfg env stack1 t1)
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (FStar_Syntax_Util.is_fstar_tactics_embed hd1) ||
                 (FStar_Syntax_Util.is_fstar_tactics_by_tactic hd1)
               ->
               let args1 = closures_as_args_delayed cfg env args in
               let hd2 = closure_as_term cfg env hd1 in
               let t2 =
                 let uu___173_10718 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.tk =
                     (uu___173_10718.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___173_10718.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___173_10718.FStar_Syntax_Syntax.vars)
                 } in
               (FStar_ST.write t2.FStar_Syntax_Syntax.tk
                  FStar_Pervasives_Native.None;
                rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____10764 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____10764) && (is_norm_request hd1 args))
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
                 let uu___174_10786 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___174_10786.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___174_10786.primitive_steps)
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
                  FStar_Syntax_Syntax.tk = uu____10794;
                  FStar_Syntax_Syntax.pos = uu____10795;
                  FStar_Syntax_Syntax.vars = uu____10796;_},a1::a2::rest)
               ->
               let uu____10860 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____10860 with
                | (hd1,uu____10880) ->
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
                    (FStar_Const.Const_reflect uu____10971);
                  FStar_Syntax_Syntax.tk = uu____10972;
                  FStar_Syntax_Syntax.pos = uu____10973;
                  FStar_Syntax_Syntax.vars = uu____10974;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____11018 = FStar_List.tl stack1 in
               norm cfg env uu____11018 (FStar_Pervasives_Native.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.tk = uu____11023;
                  FStar_Syntax_Syntax.pos = uu____11024;
                  FStar_Syntax_Syntax.vars = uu____11025;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____11069 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11069 with
                | (reify_head,uu____11089) ->
                    let a1 =
                      let uu____11119 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (FStar_Pervasives_Native.fst a) in
                      FStar_Syntax_Subst.compress uu____11119 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____11124);
                            FStar_Syntax_Syntax.tk = uu____11125;
                            FStar_Syntax_Syntax.pos = uu____11126;
                            FStar_Syntax_Syntax.vars = uu____11127;_},a2::[])
                         ->
                         norm cfg env stack1 (FStar_Pervasives_Native.fst a2)
                     | uu____11175 ->
                         let stack2 =
                           (App
                              (reify_head, FStar_Pervasives_Native.None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11187 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____11187
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11198 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11198
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____11201 =
                      let uu____11208 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11208, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11201 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___145_11222  ->
                         match uu___145_11222 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11225 =
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
                 if uu____11225 then false else should_delta in
               if Prims.op_Negation should_delta1
               then rebuild cfg env stack1 t1
               else
                 (let r_env =
                    let uu____11229 = FStar_Syntax_Syntax.range_of_fv f in
                    FStar_TypeChecker_Env.set_range cfg.tcenv uu____11229 in
                  let uu____11230 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  match uu____11230 with
                  | FStar_Pervasives_Native.None  ->
                      (log cfg
                         (fun uu____11243  ->
                            FStar_Util.print "Tm_fvar case 2\n" []);
                       rebuild cfg env stack1 t1)
                  | FStar_Pervasives_Native.Some (us,t2) ->
                      (log cfg
                         (fun uu____11254  ->
                            let uu____11255 =
                              FStar_Syntax_Print.term_to_string t0 in
                            let uu____11256 =
                              FStar_Syntax_Print.term_to_string t2 in
                            FStar_Util.print2 ">>> Unfolded %s to %s\n"
                              uu____11255 uu____11256);
                       (let t3 =
                          let uu____11258 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 (UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant)) in
                          if uu____11258
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
                          | (UnivArgs (us',uu____11268))::stack2 ->
                              let env1 =
                                FStar_All.pipe_right us'
                                  (FStar_List.fold_left
                                     (fun env1  -> fun u  -> (Univ u) :: env1)
                                     env) in
                              norm cfg env1 stack2 t3
                          | uu____11291 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack1 t3
                          | uu____11292 ->
                              let uu____11293 =
                                let uu____11294 =
                                  FStar_Syntax_Print.lid_to_string
                                    (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                FStar_Util.format1
                                  "Impossible: missing universe instantiation on %s"
                                  uu____11294 in
                              failwith uu____11293
                        else norm cfg env stack1 t3)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11297 = lookup_bvar env x in
               (match uu____11297 with
                | Univ uu____11298 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11323 = FStar_ST.read r in
                      (match uu____11323 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11358  ->
                                 let uu____11359 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____11360 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11359
                                   uu____11360);
                            (let uu____11361 =
                               let uu____11362 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____11362.FStar_Syntax_Syntax.n in
                             match uu____11361 with
                             | FStar_Syntax_Syntax.Tm_abs uu____11367 ->
                                 norm cfg env2 stack1 t'
                             | uu____11386 -> rebuild cfg env2 stack1 t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____11424)::uu____11425 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11434)::uu____11435 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11445,uu____11446))::stack_rest ->
                    (match c with
                     | Univ uu____11450 -> norm cfg (c :: env) stack_rest t1
                     | uu____11451 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____11456::[] ->
                              (match lopt with
                               | FStar_Pervasives_Native.None  when
                                   FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____11472  ->
                                         let uu____11473 =
                                           closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____11473);
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
                                           (fun uu___146_11478  ->
                                              match uu___146_11478 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____11479 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____11483  ->
                                         let uu____11484 =
                                           closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____11484);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____11485 when
                                   (FStar_All.pipe_right cfg.steps
                                      (FStar_List.contains Reify))
                                     ||
                                     (FStar_All.pipe_right cfg.steps
                                        (FStar_List.contains CheckNoUvars))
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____11488 ->
                                   let cfg1 =
                                     let uu___175_11492 = cfg in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___175_11492.tcenv);
                                       delta_level =
                                         (uu___175_11492.delta_level);
                                       primitive_steps =
                                         (uu___175_11492.primitive_steps)
                                     } in
                                   let uu____11493 =
                                     closure_as_term cfg1 env t1 in
                                   rebuild cfg1 env stack1 uu____11493)
                          | uu____11494::tl1 ->
                              (log cfg
                                 (fun uu____11513  ->
                                    let uu____11514 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11514);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___176_11548 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___176_11548.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____11569  ->
                          let uu____11570 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11570);
                     norm cfg env stack2 t1)
                | (Debug uu____11571)::uu____11572 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11575 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11575
                    else
                      (let uu____11577 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11577 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11601  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11617 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11617
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11631 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11631)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___177_11638 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___177_11638.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___177_11638.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11639 -> lopt in
                           (log cfg
                              (fun uu____11645  ->
                                 let uu____11646 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11646);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___178_11659 = cfg in
                               let uu____11660 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___178_11659.steps);
                                 tcenv = (uu___178_11659.tcenv);
                                 delta_level = (uu___178_11659.delta_level);
                                 primitive_steps = uu____11660
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____11669)::uu____11670 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11677 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11677
                    else
                      (let uu____11679 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11679 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11703  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11719 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11719
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11733 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11733)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___177_11740 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___177_11740.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___177_11740.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11741 -> lopt in
                           (log cfg
                              (fun uu____11747  ->
                                 let uu____11748 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11748);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___178_11761 = cfg in
                               let uu____11762 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___178_11761.steps);
                                 tcenv = (uu___178_11761.tcenv);
                                 delta_level = (uu___178_11761.delta_level);
                                 primitive_steps = uu____11762
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____11771)::uu____11772 ->
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
                                          let uu____11839 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11839)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___177_11846 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___177_11846.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___177_11846.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11847 -> lopt in
                           (log cfg
                              (fun uu____11853  ->
                                 let uu____11854 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11854);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___178_11867 = cfg in
                               let uu____11868 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___178_11867.steps);
                                 tcenv = (uu___178_11867.tcenv);
                                 delta_level = (uu___178_11867.delta_level);
                                 primitive_steps = uu____11868
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____11877)::uu____11878 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11887 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11887
                    else
                      (let uu____11889 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11889 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11913  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11929 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11929
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11943 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11943)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___177_11950 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___177_11950.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___177_11950.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11951 -> lopt in
                           (log cfg
                              (fun uu____11957  ->
                                 let uu____11958 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11958);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___178_11971 = cfg in
                               let uu____11972 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___178_11971.steps);
                                 tcenv = (uu___178_11971.tcenv);
                                 delta_level = (uu___178_11971.delta_level);
                                 primitive_steps = uu____11972
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____11981)::uu____11982 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11997 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11997
                    else
                      (let uu____11999 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11999 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12023  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12039 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12039
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12053 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12053)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___177_12060 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___177_12060.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___177_12060.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12061 -> lopt in
                           (log cfg
                              (fun uu____12067  ->
                                 let uu____12068 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12068);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___178_12081 = cfg in
                               let uu____12082 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___178_12081.steps);
                                 tcenv = (uu___178_12081.tcenv);
                                 delta_level = (uu___178_12081.delta_level);
                                 primitive_steps = uu____12082
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12091 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12091
                    else
                      (let uu____12093 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12093 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12117  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12133 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12133
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12147 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12147)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___177_12154 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___177_12154.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___177_12154.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12155 -> lopt in
                           (log cfg
                              (fun uu____12161  ->
                                 let uu____12162 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12162);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___178_12175 = cfg in
                               let uu____12176 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___178_12175.steps);
                                 tcenv = (uu___178_12175.tcenv);
                                 delta_level = (uu___178_12175.delta_level);
                                 primitive_steps = uu____12176
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
                      (fun uu____12231  ->
                         fun stack2  ->
                           match uu____12231 with
                           | (a,aq) ->
                               let uu____12243 =
                                 let uu____12244 =
                                   let uu____12251 =
                                     let uu____12252 =
                                       let uu____12271 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____12271, false) in
                                     Clos uu____12252 in
                                   (uu____12251, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____12244 in
                               uu____12243 :: stack2) args) in
               (log cfg
                  (fun uu____12311  ->
                     let uu____12312 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12312);
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
                             ((let uu___179_12346 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___179_12346.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___179_12346.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____12347 ->
                      let uu____12352 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12352)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____12355 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____12355 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____12382 =
                          let uu____12383 =
                            let uu____12392 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___180_12394 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___180_12394.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___180_12394.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12392) in
                          FStar_Syntax_Syntax.Tm_refine uu____12383 in
                        mk uu____12382 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____12417 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____12417
               else
                 (let uu____12419 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____12419 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12427 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12439  -> Dummy :: env1) env) in
                        norm_comp cfg uu____12427 c1 in
                      let t2 =
                        let uu____12451 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____12451 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____12532)::uu____12533 -> norm cfg env stack1 t11
                | (Arg uu____12542)::uu____12543 -> norm cfg env stack1 t11
                | (App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.tk = uu____12552;
                       FStar_Syntax_Syntax.pos = uu____12553;
                       FStar_Syntax_Syntax.vars = uu____12554;_},uu____12555,uu____12556))::uu____12557
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____12568)::uu____12569 ->
                    norm cfg env stack1 t11
                | uu____12578 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____12582  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____12605 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____12605
                        | FStar_Util.Inr c ->
                            let uu____12619 = norm_comp cfg env c in
                            FStar_Util.Inr uu____12619 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____12627 =
                        let uu____12628 =
                          let uu____12629 =
                            let uu____12664 = FStar_Syntax_Util.unascribe t12 in
                            (uu____12664, (tc1, tacopt1), l) in
                          FStar_Syntax_Syntax.Tm_ascribed uu____12629 in
                        mk uu____12628 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____12627)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____12756,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____12757;
                               FStar_Syntax_Syntax.lbunivs = uu____12758;
                               FStar_Syntax_Syntax.lbtyp = uu____12759;
                               FStar_Syntax_Syntax.lbeff = uu____12760;
                               FStar_Syntax_Syntax.lbdef = uu____12761;_}::uu____12762),uu____12763)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____12811 =
                 (let uu____12814 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____12814) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____12816 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____12816))) in
               if uu____12811
               then
                 let env1 =
                   let uu____12820 =
                     let uu____12821 =
                       let uu____12840 =
                         FStar_Util.mk_ref FStar_Pervasives_Native.None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____12840,
                         false) in
                     Clos uu____12821 in
                   uu____12820 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____12882 =
                    let uu____12887 =
                      let uu____12888 =
                        let uu____12889 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____12889
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____12888] in
                    FStar_Syntax_Subst.open_term uu____12887 body in
                  match uu____12882 with
                  | (bs,body1) ->
                      let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                      let lbname =
                        let x =
                          let uu____12903 = FStar_List.hd bs in
                          FStar_Pervasives_Native.fst uu____12903 in
                        FStar_Util.Inl
                          (let uu___181_12913 = x in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___181_12913.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___181_12913.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = ty
                           }) in
                      let lb1 =
                        let uu___182_12915 = lb in
                        let uu____12916 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = lbname;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___182_12915.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = ty;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___182_12915.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____12916
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____12935  -> Dummy :: env1)
                             env) in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let ((true ,lbs),body) when
               FStar_List.contains CompressUvars cfg.steps ->
               let uu____12962 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____12962 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____12998 =
                               let uu___183_12999 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___183_12999.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___183_12999.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____12998 in
                           let uu____13000 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____13000 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____13020 =
                                   FStar_List.map (fun uu____13024  -> Dummy)
                                     lbs1 in
                                 let uu____13025 =
                                   let uu____13028 =
                                     FStar_List.map
                                       (fun uu____13036  -> Dummy) xs1 in
                                   FStar_List.append uu____13028 env in
                                 FStar_List.append uu____13020 uu____13025 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13048 =
                                       let uu___184_13049 = rc in
                                       let uu____13050 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___184_13049.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13050;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___184_13049.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____13048
                                 | uu____13061 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___185_13065 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___185_13065.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___185_13065.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____13069 =
                        FStar_List.map (fun uu____13073  -> Dummy) lbs2 in
                      FStar_List.append uu____13069 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____13075 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____13075 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___186_13093 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.tk =
                               (uu___186_13093.FStar_Syntax_Syntax.tk);
                             FStar_Syntax_Syntax.pos =
                               (uu___186_13093.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___186_13093.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____13124 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____13124
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13147 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13198  ->
                        match uu____13198 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____13271 =
                                let uu___187_13272 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___187_13272.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___187_13272.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____13271 in
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
               (match uu____13147 with
                | (rec_env,memos,uu____13380) ->
                    let uu____13409 =
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
                             let uu____13489 =
                               let uu____13490 =
                                 let uu____13509 =
                                   FStar_Util.mk_ref
                                     FStar_Pervasives_Native.None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____13509, false) in
                               Clos uu____13490 in
                             uu____13489 :: env1)
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
                             FStar_Syntax_Syntax.tk = uu____13575;
                             FStar_Syntax_Syntax.pos = uu____13576;
                             FStar_Syntax_Syntax.vars = uu____13577;_},uu____13578,uu____13579))::uu____13580
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____13591 -> false in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____13601 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____13601
                        then
                          let uu___188_13602 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___188_13602.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps =
                              (uu___188_13602.primitive_steps)
                          }
                        else
                          (let uu___189_13604 = cfg in
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___189_13604.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta];
                             primitive_steps =
                               (uu___189_13604.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____13606 =
                         let uu____13607 = FStar_Syntax_Subst.compress head1 in
                         uu____13607.FStar_Syntax_Syntax.n in
                       match uu____13606 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____13631 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____13631 with
                            | (uu____13632,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____13638 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____13646 =
                                         let uu____13647 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____13647.FStar_Syntax_Syntax.n in
                                       match uu____13646 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____13655,uu____13656))
                                           ->
                                           let uu____13673 =
                                             let uu____13674 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____13674.FStar_Syntax_Syntax.n in
                                           (match uu____13673 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____13682,msrc,uu____13684))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____13701 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____13701
                                            | uu____13702 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____13703 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____13704 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____13704 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___190_13709 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___190_13709.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___190_13709.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___190_13709.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____13710 =
                                            FStar_List.tl stack1 in
                                          let uu____13711 =
                                            let uu____13712 =
                                              let uu____13717 =
                                                let uu____13718 =
                                                  let uu____13733 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____13733) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____13718 in
                                              FStar_Syntax_Syntax.mk
                                                uu____13717 in
                                            uu____13712
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____13710
                                            uu____13711
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____13754 =
                                            let uu____13755 = is_return body in
                                            match uu____13755 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____13759;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____13760;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____13761;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____13770 -> false in
                                          if uu____13754
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
                                               let uu____13810 =
                                                 let uu____13815 =
                                                   let uu____13816 =
                                                     let uu____13835 =
                                                       let uu____13838 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____13838] in
                                                     (uu____13835, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc)) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____13816 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____13815 in
                                               uu____13810
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____13859 =
                                                 let uu____13860 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____13860.FStar_Syntax_Syntax.n in
                                               match uu____13859 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____13870::uu____13871::[])
                                                   ->
                                                   let uu____13882 =
                                                     let uu____13887 =
                                                       let uu____13888 =
                                                         let uu____13897 =
                                                           let uu____13900 =
                                                             let uu____13901
                                                               =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____13901 in
                                                           let uu____13902 =
                                                             let uu____13905
                                                               =
                                                               let uu____13906
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____13906 in
                                                             [uu____13905] in
                                                           uu____13900 ::
                                                             uu____13902 in
                                                         (bind1, uu____13897) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____13888 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____13887 in
                                                   uu____13882
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____13917 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____13927 =
                                                 let uu____13932 =
                                                   let uu____13933 =
                                                     let uu____13952 =
                                                       let uu____13955 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____13956 =
                                                         let uu____13959 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____13960 =
                                                           let uu____13963 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____13964 =
                                                             let uu____13967
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____13968
                                                               =
                                                               let uu____13971
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____13972
                                                                 =
                                                                 let uu____13975
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____13975] in
                                                               uu____13971 ::
                                                                 uu____13972 in
                                                             uu____13967 ::
                                                               uu____13968 in
                                                           uu____13963 ::
                                                             uu____13964 in
                                                         uu____13959 ::
                                                           uu____13960 in
                                                       uu____13955 ::
                                                         uu____13956 in
                                                     (bind_inst, uu____13952) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____13933 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____13932 in
                                               uu____13927
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____13986 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____13986 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____14018 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____14018 with
                            | (uu____14019,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____14054 =
                                        let uu____14055 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____14055.FStar_Syntax_Syntax.n in
                                      match uu____14054 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____14065) -> t4
                                      | uu____14074 -> head2 in
                                    let uu____14075 =
                                      let uu____14076 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____14076.FStar_Syntax_Syntax.n in
                                    match uu____14075 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____14084 ->
                                        FStar_Pervasives_Native.None in
                                  let uu____14085 = maybe_extract_fv head2 in
                                  match uu____14085 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____14095 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____14095
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____14100 =
                                          maybe_extract_fv head3 in
                                        match uu____14100 with
                                        | FStar_Pervasives_Native.Some
                                            uu____14105 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____14106 ->
                                            FStar_Pervasives_Native.Some
                                              false in
                                      (head3, action_unfolded)
                                  | uu____14111 ->
                                      (head2, FStar_Pervasives_Native.None) in
                                ((let is_arg_impure uu____14128 =
                                    match uu____14128 with
                                    | (e,q) ->
                                        let uu____14135 =
                                          let uu____14136 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____14136.FStar_Syntax_Syntax.n in
                                        (match uu____14135 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____14161 -> false) in
                                  let uu____14162 =
                                    let uu____14163 =
                                      let uu____14170 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____14170 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____14163 in
                                  if uu____14162
                                  then
                                    let uu____14175 =
                                      let uu____14176 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____14176 in
                                    failwith uu____14175
                                  else ());
                                 (let uu____14178 =
                                    maybe_unfold_action head_app in
                                  match uu____14178 with
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
                                      let uu____14231 = FStar_List.tl stack1 in
                                      norm cfg env uu____14231 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____14253 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____14253 in
                           let uu____14254 = FStar_List.tl stack1 in
                           norm cfg env uu____14254 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____14407  ->
                                     match uu____14407 with
                                     | (pat,wopt,tm) ->
                                         let uu____14471 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____14471))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____14517 = FStar_List.tl stack1 in
                           norm cfg env uu____14517 tm
                       | uu____14518 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.tk = uu____14531;
                             FStar_Syntax_Syntax.pos = uu____14532;
                             FStar_Syntax_Syntax.vars = uu____14533;_},uu____14534,uu____14535))::uu____14536
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____14547 -> false in
                    if should_reify
                    then
                      let uu____14548 = FStar_List.tl stack1 in
                      let uu____14549 =
                        let uu____14550 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____14550 in
                      norm cfg env uu____14548 uu____14549
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____14553 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____14553
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___191_14562 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___191_14562.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___191_14562.primitive_steps)
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
                | uu____14564 ->
                    (match stack1 with
                     | uu____14565::uu____14566 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled
                              (l,r,uu____14571) ->
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
                          | uu____14600 -> norm cfg env stack1 head1)
                     | [] ->
                         let head2 = norm cfg env [] head1 in
                         let m1 =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               let uu____14616 =
                                 norm_pattern_args cfg env args in
                               FStar_Syntax_Syntax.Meta_pattern uu____14616
                           | uu____14629 -> m in
                         let t2 =
                           mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                             t1.FStar_Syntax_Syntax.pos in
                         rebuild cfg env stack1 t2)))
and reify_lift:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
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
              let uu____14645 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____14645 with
              | (uu____14646,return_repr) ->
                  let return_inst =
                    let uu____14657 =
                      let uu____14658 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____14658.FStar_Syntax_Syntax.n in
                    match uu____14657 with
                    | FStar_Syntax_Syntax.Tm_uinst
                        (return_tm,uu____14668::[]) ->
                        let uu____14679 =
                          let uu____14684 =
                            let uu____14685 =
                              let uu____14694 =
                                let uu____14697 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____14697] in
                              (return_tm, uu____14694) in
                            FStar_Syntax_Syntax.Tm_uinst uu____14685 in
                          FStar_Syntax_Syntax.mk uu____14684 in
                        uu____14679 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____14708 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____14713 =
                    let uu____14718 =
                      let uu____14719 =
                        let uu____14738 =
                          let uu____14741 = FStar_Syntax_Syntax.as_arg t in
                          let uu____14742 =
                            let uu____14745 = FStar_Syntax_Syntax.as_arg e in
                            [uu____14745] in
                          uu____14741 :: uu____14742 in
                        (return_inst, uu____14738) in
                      FStar_Syntax_Syntax.Tm_app uu____14719 in
                    FStar_Syntax_Syntax.mk uu____14718 in
                  uu____14713 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____14757 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____14757 with
               | FStar_Pervasives_Native.None  ->
                   let uu____14760 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____14760
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____14761;
                     FStar_TypeChecker_Env.mtarget = uu____14762;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____14763;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____14774;
                     FStar_TypeChecker_Env.mtarget = uu____14775;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____14776;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____14794 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____14794)
and norm_pattern_args:
  cfg ->
    env ->
      ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
         FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list Prims.list ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
          FStar_Pervasives_Native.tuple2 Prims.list Prims.list
  =
  fun cfg  ->
    fun env  ->
      fun args  ->
        FStar_All.pipe_right args
          (FStar_List.map
             (FStar_List.map
                (fun uu____14854  ->
                   match uu____14854 with
                   | (a,imp) ->
                       let uu____14865 = norm cfg env [] a in
                       (uu____14865, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___192_14888 = comp1 in
            let uu____14893 =
              let uu____14894 =
                let uu____14905 = norm cfg env [] t in
                let uu____14906 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____14905, uu____14906) in
              FStar_Syntax_Syntax.Total uu____14894 in
            {
              FStar_Syntax_Syntax.n = uu____14893;
              FStar_Syntax_Syntax.tk =
                (uu___192_14888.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___192_14888.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___192_14888.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___193_14925 = comp1 in
            let uu____14930 =
              let uu____14931 =
                let uu____14942 = norm cfg env [] t in
                let uu____14943 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____14942, uu____14943) in
              FStar_Syntax_Syntax.GTotal uu____14931 in
            {
              FStar_Syntax_Syntax.n = uu____14930;
              FStar_Syntax_Syntax.tk =
                (uu___193_14925.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___193_14925.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___193_14925.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____14995  ->
                      match uu____14995 with
                      | (a,i) ->
                          let uu____15006 = norm cfg env [] a in
                          (uu____15006, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___147_15017  ->
                      match uu___147_15017 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____15023 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____15023
                      | f -> f)) in
            let uu___194_15029 = comp1 in
            let uu____15034 =
              let uu____15035 =
                let uu___195_15036 = ct in
                let uu____15037 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____15038 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____15043 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____15037;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___195_15036.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____15038;
                  FStar_Syntax_Syntax.effect_args = uu____15043;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____15035 in
            {
              FStar_Syntax_Syntax.n = uu____15034;
              FStar_Syntax_Syntax.tk =
                (uu___194_15029.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___194_15029.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___194_15029.FStar_Syntax_Syntax.vars)
            }
and ghost_to_pure_aux:
  cfg ->
    env ->
      FStar_Syntax_Syntax.comp ->
        (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun cfg  ->
    fun env  ->
      fun c  ->
        let norm1 t =
          norm
            (let uu___196_15063 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___196_15063.tcenv);
               delta_level = (uu___196_15063.delta_level);
               primitive_steps = (uu___196_15063.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____15068 = norm1 t in
          FStar_Syntax_Util.non_informative uu____15068 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____15073 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___197_15098 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.tk =
                (uu___197_15098.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___197_15098.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___197_15098.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____15107 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____15107
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
                    let uu___198_15120 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___198_15120.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___198_15120.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___198_15120.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___199_15122 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___199_15122.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___199_15122.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___199_15122.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___199_15122.FStar_Syntax_Syntax.flags)
                    } in
              let uu___200_15123 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.tk =
                  (uu___200_15123.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___200_15123.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___200_15123.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____15125 -> c
and norm_binder:
  cfg ->
    env ->
      FStar_Syntax_Syntax.binder ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
          FStar_Pervasives_Native.tuple2
  =
  fun cfg  ->
    fun env  ->
      fun uu____15128  ->
        match uu____15128 with
        | (x,imp) ->
            let uu____15131 =
              let uu___201_15132 = x in
              let uu____15133 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___201_15132.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___201_15132.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____15133
              } in
            (uu____15131, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____15141 =
          FStar_List.fold_left
            (fun uu____15159  ->
               fun b  ->
                 match uu____15159 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____15141 with | (nbs,uu____15187) -> FStar_List.rev nbs
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
            let uu____15203 =
              let uu___202_15204 = rc in
              let uu____15205 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___202_15204.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____15205;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___202_15204.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____15203
        | uu____15216 -> lopt
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
              ((let uu____15228 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____15228
                then
                  let uu____15229 = FStar_Syntax_Print.term_to_string tm in
                  let uu____15230 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2 "Normalized %s to %s\n" uu____15229
                    uu____15230
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___203_15248 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___203_15248.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____15279  ->
                    let uu____15280 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____15280);
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
              let uu____15318 =
                let uu___204_15319 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___204_15319.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___204_15319.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___204_15319.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____15318
          | (Arg (Univ uu____15320,uu____15321,uu____15322))::uu____15323 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____15326,uu____15327))::uu____15328 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____15344),aq,r))::stack2 ->
              (log cfg
                 (fun uu____15373  ->
                    let uu____15374 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____15374);
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
                 (let uu____15386 = FStar_ST.read m in
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
                  | FStar_Pervasives_Native.Some (uu____15424,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq)
                          FStar_Pervasives_Native.None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 =
                FStar_Syntax_Syntax.extend_app head1 (t, aq)
                  FStar_Pervasives_Native.None r in
              let uu____15452 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____15452
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____15462  ->
                    let uu____15463 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____15463);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____15468 =
                  log cfg
                    (fun uu____15473  ->
                       let uu____15474 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____15475 =
                         let uu____15476 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____15493  ->
                                   match uu____15493 with
                                   | (p,uu____15503,uu____15504) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____15476
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____15474 uu____15475);
                  (let whnf = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___148_15521  ->
                               match uu___148_15521 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____15522 -> false)) in
                     let steps' =
                       let uu____15526 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____15526
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___205_15530 = cfg in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___205_15530.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___205_15530.primitive_steps)
                     } in
                   let norm_or_whnf env2 t1 =
                     if whnf
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____15574 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____15597 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____15663  ->
                                   fun uu____15664  ->
                                     match (uu____15663, uu____15664) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____15767 = norm_pat env3 p1 in
                                         (match uu____15767 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____15597 with
                          | (pats1,env3) ->
                              ((let uu___206_15869 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.p =
                                    (uu___206_15869.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___207_15888 = x in
                           let uu____15889 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___207_15888.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___207_15888.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____15889
                           } in
                         ((let uu___208_15899 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.p =
                               (uu___208_15899.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___209_15904 = x in
                           let uu____15905 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___209_15904.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___209_15904.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____15905
                           } in
                         ((let uu___210_15915 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.p =
                               (uu___210_15915.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___211_15929 = x in
                           let uu____15930 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___211_15929.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___211_15929.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____15930
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___212_15941 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.p =
                               (uu___212_15941.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf -> branches
                     | uu____15945 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____15959 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____15959 with
                                 | (p,wopt,e) ->
                                     let uu____15987 = norm_pat env1 p in
                                     (match uu____15987 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Pervasives_Native.Some w
                                                ->
                                                let uu____16024 =
                                                  norm_or_whnf env2 w in
                                                FStar_Pervasives_Native.Some
                                                  uu____16024 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____16030 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____16030) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____16044) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____16053 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____16054;
                        FStar_Syntax_Syntax.fv_delta = uu____16055;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Data_ctor );_}
                      -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____16056;
                        FStar_Syntax_Syntax.fv_delta = uu____16057;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Record_ctor uu____16058);_}
                      -> true
                  | uu____16065 -> false in
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
                  let uu____16228 =
                    FStar_Syntax_Util.head_and_args scrutinee1 in
                  match uu____16228 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var uu____16289 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_wild uu____16292 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____16295 ->
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
                            | uu____16352 ->
                                let uu____16353 =
                                  let uu____16354 = is_cons head1 in
                                  Prims.op_Negation uu____16354 in
                                FStar_Util.Inr uu____16353))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____16411)::rest_a,(p1,uu____16414)::rest_p) ->
                      let uu____16468 = matches_pat t1 p1 in
                      (match uu____16468 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____16493 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____16623 = matches_pat scrutinee1 p1 in
                      (match uu____16623 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____16643  ->
                                 let uu____16644 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____16645 =
                                   let uu____16646 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____16646
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____16644 uu____16645);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____16663 =
                                        let uu____16664 =
                                          let uu____16683 =
                                            FStar_Util.mk_ref
                                              (FStar_Pervasives_Native.Some
                                                 ([], t1)) in
                                          ([], t1, uu____16683, false) in
                                        Clos uu____16664 in
                                      uu____16663 :: env2) env1 s in
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
             (fun uu___149_16748  ->
                match uu___149_16748 with
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
            let uu___213_16787 = config s e in
            {
              steps = (uu___213_16787.steps);
              tcenv = (uu___213_16787.tcenv);
              delta_level = (uu___213_16787.delta_level);
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
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
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
            let uu___214_16847 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___214_16847.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___214_16847.FStar_Syntax_Syntax.cflags);
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
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____16870);
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
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____16890);
             c) in
      FStar_Syntax_Print.comp_to_string c1
let normalize_refinement:
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
          FStar_Syntax_Syntax.syntax
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
                   let uu____16946 =
                     let uu____16947 =
                       let uu____16956 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____16956) in
                     FStar_Syntax_Syntax.Tm_refine uu____16947 in
                   mk uu____16946 t01.FStar_Syntax_Syntax.pos
               | uu____16965 -> t2)
          | uu____16966 -> t2 in
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
        let uu____17018 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____17018 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____17047 ->
                 let uu____17054 = FStar_Syntax_Util.abs_formals e in
                 (match uu____17054 with
                  | (actuals,uu____17064,uu____17065) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____17079 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____17079 with
                         | (binders,args) ->
                             let uu____17096 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____17096
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c)))))
let eta_expand:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____17105 =
        let uu____17112 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
        (uu____17112, (t.FStar_Syntax_Syntax.n)) in
      match uu____17105 with
      | (FStar_Pervasives_Native.Some sort,uu____17120) ->
          let uu____17123 = mk sort t.FStar_Syntax_Syntax.pos in
          eta_expand_with_type env t uu____17123
      | (uu____17124,FStar_Syntax_Syntax.Tm_name x) ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____17130 ->
          let uu____17137 = FStar_Syntax_Util.head_and_args t in
          (match uu____17137 with
           | (head1,args) ->
               let uu____17186 =
                 let uu____17187 = FStar_Syntax_Subst.compress head1 in
                 uu____17187.FStar_Syntax_Syntax.n in
               (match uu____17186 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____17192,thead) ->
                    let uu____17226 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____17226 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____17276 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___219_17284 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___219_17284.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___219_17284.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___219_17284.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___219_17284.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___219_17284.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___219_17284.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___219_17284.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___219_17284.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___219_17284.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___219_17284.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___219_17284.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___219_17284.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___219_17284.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___219_17284.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___219_17284.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___219_17284.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___219_17284.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___219_17284.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___219_17284.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___219_17284.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___219_17284.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___219_17284.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___219_17284.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___219_17284.FStar_TypeChecker_Env.is_native_tactic)
                                 }) t in
                            match uu____17276 with
                            | (uu____17285,ty,uu____17287) ->
                                eta_expand_with_type env t ty))
                | uu____17288 ->
                    let uu____17289 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___220_17297 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___220_17297.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___220_17297.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___220_17297.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___220_17297.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___220_17297.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___220_17297.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___220_17297.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___220_17297.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___220_17297.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___220_17297.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___220_17297.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___220_17297.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___220_17297.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___220_17297.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___220_17297.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___220_17297.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___220_17297.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___220_17297.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___220_17297.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___220_17297.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___220_17297.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___220_17297.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___220_17297.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___220_17297.FStar_TypeChecker_Env.is_native_tactic)
                         }) t in
                    (match uu____17289 with
                     | (uu____17298,ty,uu____17300) ->
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
                                                         (FStar_Syntax_Syntax.comp',
                                                           Prims.unit)
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
            | (uu____17380,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____17386,FStar_Util.Inl t) ->
                let uu____17392 =
                  let uu____17397 =
                    let uu____17398 =
                      let uu____17413 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____17413) in
                    FStar_Syntax_Syntax.Tm_arrow uu____17398 in
                  FStar_Syntax_Syntax.mk uu____17397 in
                uu____17392 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____17418 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____17418 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____17447 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____17510 ->
                    let uu____17511 =
                      let uu____17520 =
                        let uu____17521 = FStar_Syntax_Subst.compress t3 in
                        uu____17521.FStar_Syntax_Syntax.n in
                      (uu____17520, tc) in
                    (match uu____17511 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____17550) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____17595) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____17646,FStar_Util.Inl uu____17647) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____17674 -> failwith "Impossible") in
              (match uu____17447 with
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
          let uu____17793 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____17793 with
          | (univ_names1,binders1,tc) ->
              let uu____17857 = FStar_Util.left tc in
              (univ_names1, binders1, uu____17857)
let elim_uvars_aux_c:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,(FStar_Syntax_Syntax.comp',
                                                         Prims.unit)
                                                         FStar_Syntax_Syntax.syntax)
            FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun c  ->
          let uu____17900 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____17900 with
          | (univ_names1,binders1,tc) ->
              let uu____17968 = FStar_Util.right tc in
              (univ_names1, binders1, uu____17968)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____18009 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____18009 with
           | (univ_names1,binders1,typ1) ->
               let uu___221_18037 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___221_18037.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___221_18037.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___221_18037.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___221_18037.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___222_18058 = s in
          let uu____18059 =
            let uu____18060 =
              let uu____18069 = FStar_List.map (elim_uvars env) sigs in
              (uu____18069, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____18060 in
          {
            FStar_Syntax_Syntax.sigel = uu____18059;
            FStar_Syntax_Syntax.sigrng =
              (uu___222_18058.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___222_18058.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___222_18058.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___222_18058.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____18086 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____18086 with
           | (univ_names1,uu____18104,typ1) ->
               let uu___223_18118 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___223_18118.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___223_18118.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___223_18118.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___223_18118.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____18124 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____18124 with
           | (univ_names1,uu____18142,typ1) ->
               let uu___224_18156 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___224_18156.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___224_18156.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___224_18156.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___224_18156.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____18190 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____18190 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____18213 =
                            let uu____18214 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____18214 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____18213 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___225_18217 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___225_18217.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___225_18217.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___226_18218 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___226_18218.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___226_18218.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___226_18218.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___226_18218.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___227_18230 = s in
          let uu____18231 =
            let uu____18232 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____18232 in
          {
            FStar_Syntax_Syntax.sigel = uu____18231;
            FStar_Syntax_Syntax.sigrng =
              (uu___227_18230.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___227_18230.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___227_18230.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___227_18230.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____18236 = elim_uvars_aux_t env us [] t in
          (match uu____18236 with
           | (us1,uu____18254,t1) ->
               let uu___228_18268 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___228_18268.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___228_18268.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___228_18268.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___228_18268.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____18269 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____18271 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____18271 with
           | (univs1,binders,signature) ->
               let uu____18299 =
                 let uu____18308 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____18308 with
                 | (univs_opening,univs2) ->
                     let uu____18335 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____18335) in
               (match uu____18299 with
                | (univs_opening,univs_closing) ->
                    let uu____18352 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____18358 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____18359 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____18358, uu____18359) in
                    (match uu____18352 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____18381 =
                           match uu____18381 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____18399 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____18399 with
                                | (us1,t1) ->
                                    let uu____18410 =
                                      let uu____18415 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____18422 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____18415, uu____18422) in
                                    (match uu____18410 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____18435 =
                                           let uu____18440 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____18449 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____18440, uu____18449) in
                                         (match uu____18435 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____18465 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____18465 in
                                              let uu____18466 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____18466 with
                                               | (uu____18487,uu____18488,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____18503 =
                                                       let uu____18504 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____18504 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____18503 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____18509 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____18509 with
                           | (uu____18522,uu____18523,t1) -> t1 in
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
                             | uu____18601 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____18624 =
                               let uu____18625 =
                                 FStar_Syntax_Subst.compress body in
                               uu____18625.FStar_Syntax_Syntax.n in
                             match uu____18624 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____18718 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____18755 =
                               let uu____18756 =
                                 FStar_Syntax_Subst.compress t in
                               uu____18756.FStar_Syntax_Syntax.n in
                             match uu____18755 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____18783) ->
                                 let uu____18808 = destruct_action_body body in
                                 (match uu____18808 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____18873 ->
                                 let uu____18874 = destruct_action_body t in
                                 (match uu____18874 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____18943 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____18943 with
                           | (action_univs,t) ->
                               let uu____18954 = destruct_action_typ_templ t in
                               (match uu____18954 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___229_19007 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___229_19007.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___229_19007.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___230_19009 = ed in
                           let uu____19010 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____19011 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____19012 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____19013 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____19014 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____19015 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____19016 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____19017 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____19018 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____19019 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____19020 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____19021 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____19022 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____19023 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___230_19009.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___230_19009.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____19010;
                             FStar_Syntax_Syntax.bind_wp = uu____19011;
                             FStar_Syntax_Syntax.if_then_else = uu____19012;
                             FStar_Syntax_Syntax.ite_wp = uu____19013;
                             FStar_Syntax_Syntax.stronger = uu____19014;
                             FStar_Syntax_Syntax.close_wp = uu____19015;
                             FStar_Syntax_Syntax.assert_p = uu____19016;
                             FStar_Syntax_Syntax.assume_p = uu____19017;
                             FStar_Syntax_Syntax.null_wp = uu____19018;
                             FStar_Syntax_Syntax.trivial = uu____19019;
                             FStar_Syntax_Syntax.repr = uu____19020;
                             FStar_Syntax_Syntax.return_repr = uu____19021;
                             FStar_Syntax_Syntax.bind_repr = uu____19022;
                             FStar_Syntax_Syntax.actions = uu____19023
                           } in
                         let uu___231_19026 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___231_19026.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___231_19026.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___231_19026.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___231_19026.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___150_19043 =
            match uu___150_19043 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____19070 = elim_uvars_aux_t env us [] t in
                (match uu____19070 with
                 | (us1,uu____19094,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___232_19113 = sub_eff in
            let uu____19114 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____19117 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___232_19113.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___232_19113.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____19114;
              FStar_Syntax_Syntax.lift = uu____19117
            } in
          let uu___233_19120 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___233_19120.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___233_19120.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___233_19120.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___233_19120.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____19130 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____19130 with
           | (univ_names1,binders1,comp1) ->
               let uu___234_19170 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___234_19170.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___234_19170.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___234_19170.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___234_19170.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____19183 -> s