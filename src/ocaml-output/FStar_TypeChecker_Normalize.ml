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
    match projectee with | Clos _0 -> true | uu____243 -> false
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
    match projectee with | Univ _0 -> true | uu____284 -> false
let __proj__Univ__item___0: closure -> FStar_Syntax_Syntax.universe =
  fun projectee  -> match projectee with | Univ _0 -> _0
let uu___is_Dummy: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____297 -> false
type env = closure Prims.list
let closure_to_string: closure -> Prims.string =
  fun uu___138_302  ->
    match uu___138_302 with
    | Clos (uu____303,t,uu____305,uu____306) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____317 -> "Univ"
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
    match projectee with | Arg _0 -> true | uu____467 -> false
let __proj__Arg__item___0:
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Arg _0 -> _0
let uu___is_UnivArgs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____493 -> false
let __proj__UnivArgs__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____519 -> false
let __proj__MemoLazy__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0
let uu___is_Match: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____548 -> false
let __proj__Match__item___0:
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Abs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____577 -> false
let __proj__Abs__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____612 -> false
let __proj__App__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Meta: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____637 -> false
let __proj__Meta__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Meta _0 -> _0
let uu___is_Let: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____661 -> false
let __proj__Let__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Steps: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Steps _0 -> true | uu____692 -> false
let __proj__Steps__item___0:
  stack_elt ->
    (steps,primitive_step Prims.list,FStar_TypeChecker_Env.delta_level
                                       Prims.list)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Steps _0 -> _0
let uu___is_Debug: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____721 -> false
let __proj__Debug__item___0: stack_elt -> FStar_Syntax_Syntax.term =
  fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list
let mk t r = FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r
let set_memo r t =
  let uu____777 = FStar_ST.read r in
  match uu____777 with
  | FStar_Pervasives_Native.Some uu____782 ->
      failwith "Unexpected set_memo: thunk already evaluated"
  | FStar_Pervasives_Native.None  ->
      FStar_ST.write r (FStar_Pervasives_Native.Some t)
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____792 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____792 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___139_798  ->
    match uu___139_798 with
    | Arg (c,uu____800,uu____801) ->
        let uu____802 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____802
    | MemoLazy uu____803 -> "MemoLazy"
    | Abs (uu____807,bs,uu____809,uu____810,uu____811) ->
        let uu____814 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____814
    | UnivArgs uu____821 -> "UnivArgs"
    | Match uu____825 -> "Match"
    | App (t,uu____830,uu____831) ->
        let uu____832 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____832
    | Meta (m,uu____834) -> "Meta"
    | Let uu____835 -> "Let"
    | Steps (uu____840,uu____841,uu____842) -> "Steps"
    | Debug t ->
        let uu____848 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____848
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____855 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____855 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____871 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____871 then f () else ()
let is_empty uu___140_882 =
  match uu___140_882 with | [] -> true | uu____884 -> false
let lookup_bvar env x =
  try FStar_List.nth env x.FStar_Syntax_Syntax.index
  with
  | uu____909 ->
      let uu____910 =
        let uu____911 = FStar_Syntax_Print.db_to_string x in
        FStar_Util.format1 "Failed to find %s\n" uu____911 in
      failwith uu____910
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
          let uu____946 =
            FStar_List.fold_left
              (fun uu____964  ->
                 fun u1  ->
                   match uu____964 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____979 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____979 with
                        | (k_u,n1) ->
                            let uu____988 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____988
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____946 with
          | (uu____998,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____1017 = FStar_List.nth env x in
                 match uu____1017 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____1020 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____1027 ->
                   let uu____1028 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____1028
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____1032 when
              FStar_All.pipe_right cfg.steps
                (FStar_List.contains CheckNoUvars)
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1037 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1042 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1047 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____1047 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____1058 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____1058 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____1063 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____1070 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____1070 with
                                  | (uu____1073,m) -> n1 <= m)) in
                        if uu____1063 then rest1 else us1
                    | uu____1077 -> us1)
               | uu____1080 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1083 = aux u3 in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____1083 in
        let uu____1085 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____1085
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1087 = aux u in
           match uu____1087 with
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
          (fun uu____1178  ->
             let uu____1179 = FStar_Syntax_Print.tag_of_term t in
             let uu____1180 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1179
               uu____1180);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1181 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1184 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  ->
                  (FStar_ST.write t1.FStar_Syntax_Syntax.tk
                     FStar_Pervasives_Native.None;
                   t1)
              | FStar_Syntax_Syntax.Tm_constant uu____1203 ->
                  (FStar_ST.write t1.FStar_Syntax_Syntax.tk
                     FStar_Pervasives_Native.None;
                   t1)
              | FStar_Syntax_Syntax.Tm_name uu____1208 ->
                  (FStar_ST.write t1.FStar_Syntax_Syntax.tk
                     FStar_Pervasives_Native.None;
                   t1)
              | FStar_Syntax_Syntax.Tm_fvar uu____1213 ->
                  (FStar_ST.write t1.FStar_Syntax_Syntax.tk
                     FStar_Pervasives_Native.None;
                   t1)
              | FStar_Syntax_Syntax.Tm_uvar uu____1218 ->
                  let uu____1229 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains CheckNoUvars) in
                  if uu____1229
                  then
                    let uu____1230 =
                      let uu____1231 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos in
                      let uu____1232 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____1231 uu____1232 in
                    failwith uu____1230
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____1235 =
                    let uu____1236 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____1236 in
                  mk uu____1235 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____1243 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____1243
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____1245 = lookup_bvar env x in
                  (match uu____1245 with
                   | Univ uu____1246 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____1250) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____1308 = closures_as_binders_delayed cfg env bs in
                  (match uu____1308 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____1328 =
                         let uu____1329 =
                           let uu____1339 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____1339) in
                         FStar_Syntax_Syntax.Tm_abs uu____1329 in
                       mk uu____1328 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____1359 = closures_as_binders_delayed cfg env bs in
                  (match uu____1359 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____1390 =
                    let uu____1397 =
                      let uu____1401 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____1401] in
                    closures_as_binders_delayed cfg env uu____1397 in
                  (match uu____1390 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____1415 =
                         let uu____1416 =
                           let uu____1421 =
                             let uu____1422 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____1422
                               FStar_Pervasives_Native.fst in
                           (uu____1421, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____1416 in
                       mk uu____1415 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____1490 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____1490
                    | FStar_Util.Inr c ->
                        let uu____1504 = close_comp cfg env c in
                        FStar_Util.Inr uu____1504 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____1519 =
                    let uu____1520 =
                      let uu____1538 = closure_as_term_delayed cfg env t11 in
                      (uu____1538, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____1520 in
                  mk uu____1519 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____1576 =
                    let uu____1577 =
                      let uu____1582 = closure_as_term_delayed cfg env t' in
                      let uu____1585 =
                        let uu____1586 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____1586 in
                      (uu____1582, uu____1585) in
                    FStar_Syntax_Syntax.Tm_meta uu____1577 in
                  mk uu____1576 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____1628 =
                    let uu____1629 =
                      let uu____1634 = closure_as_term_delayed cfg env t' in
                      let uu____1637 =
                        let uu____1638 =
                          let uu____1643 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____1643) in
                        FStar_Syntax_Syntax.Meta_monadic uu____1638 in
                      (uu____1634, uu____1637) in
                    FStar_Syntax_Syntax.Tm_meta uu____1629 in
                  mk uu____1628 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____1662 =
                    let uu____1663 =
                      let uu____1668 = closure_as_term_delayed cfg env t' in
                      let uu____1671 =
                        let uu____1672 =
                          let uu____1678 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____1678) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____1672 in
                      (uu____1668, uu____1671) in
                    FStar_Syntax_Syntax.Tm_meta uu____1663 in
                  mk uu____1662 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____1691 =
                    let uu____1692 =
                      let uu____1697 = closure_as_term_delayed cfg env t' in
                      (uu____1697, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____1692 in
                  mk uu____1691 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____1720  -> Dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let uu____1726 =
                    let uu____1733 = FStar_Syntax_Syntax.is_top_level [lb] in
                    if uu____1733
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       let uu____1746 =
                         closure_as_term cfg (Dummy :: env0) body in
                       ((FStar_Util.Inl
                           (let uu___155_1750 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___155_1750.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___155_1750.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____1746)) in
                  (match uu____1726 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___156_1762 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___156_1762.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___156_1762.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         } in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____1769,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____1795  -> fun env2  -> Dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____1800 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____1800
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____1806  -> fun env2  -> Dummy :: env2) lbs
                          env_univs in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let nm =
                      let uu____1813 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____1813
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         FStar_All.pipe_right
                           (let uu___157_1821 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___157_1821.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___157_1821.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41)) in
                    let uu___158_1822 = lb in
                    let uu____1823 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___158_1822.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___158_1822.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____1823
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____1836  -> fun env1  -> Dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____1887 =
                    match uu____1887 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____1925 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____1938 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____1976  ->
                                        fun uu____1977  ->
                                          match (uu____1976, uu____1977) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____2031 =
                                                norm_pat env3 p1 in
                                              (match uu____2031 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____1938 with
                               | (pats1,env3) ->
                                   ((let uu___159_2085 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___159_2085.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___160_2096 = x in
                                let uu____2097 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___160_2096.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___160_2096.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____2097
                                } in
                              ((let uu___161_2103 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___161_2103.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___162_2107 = x in
                                let uu____2108 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___162_2107.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___162_2107.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____2108
                                } in
                              ((let uu___163_2114 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___163_2114.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___164_2123 = x in
                                let uu____2124 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___164_2123.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___164_2123.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____2124
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___165_2131 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___165_2131.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____2133 = norm_pat env1 pat in
                        (match uu____2133 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____2153 =
                                     closure_as_term cfg env2 w in
                                   FStar_Pervasives_Native.Some uu____2153 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____2157 =
                    let uu____2158 =
                      let uu____2173 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____2173) in
                    FStar_Syntax_Syntax.Tm_match uu____2158 in
                  mk uu____2157 t1.FStar_Syntax_Syntax.pos))
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
        | uu____2220 -> closure_as_term cfg env t
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
        | uu____2236 ->
            FStar_List.map
              (fun uu____2250  ->
                 match uu____2250 with
                 | (x,imp) ->
                     let uu____2265 = closure_as_term_delayed cfg env x in
                     (uu____2265, imp)) args
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
        let uu____2277 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____2309  ->
                  fun uu____2310  ->
                    match (uu____2309, uu____2310) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___166_2354 = b in
                          let uu____2355 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___166_2354.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___166_2354.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____2355
                          } in
                        let env2 = Dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____2277 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____2402 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____2414 = closure_as_term_delayed cfg env t in
                 let uu____2415 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____2414 uu____2415
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____2425 = closure_as_term_delayed cfg env t in
                 let uu____2426 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____2425 uu____2426
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
                        (fun uu___141_2445  ->
                           match uu___141_2445 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____2449 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____2449
                           | f -> f)) in
                 let uu____2453 =
                   let uu___167_2454 = c1 in
                   let uu____2455 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____2455;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___167_2454.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____2453)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags  ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___142_2462  ->
            match uu___142_2462 with
            | FStar_Syntax_Syntax.DECREASES uu____2463 -> false
            | uu____2466 -> true))
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
                   (fun uu___143_2480  ->
                      match uu___143_2480 with
                      | FStar_Syntax_Syntax.DECREASES uu____2481 -> false
                      | uu____2484 -> true)) in
            let rc1 =
              let uu___168_2486 = rc in
              let uu____2487 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___168_2486.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____2487;
                FStar_Syntax_Syntax.residual_flags = flags
              } in
            FStar_Pervasives_Native.Some rc1
        | uu____2493 -> lopt
let built_in_primitive_steps: primitive_step Prims.list =
  let const_as_tm c p = mk (FStar_Syntax_Syntax.Tm_constant c) p in
  let int_as_const p i =
    let uu____2512 =
      let uu____2513 =
        let uu____2519 = FStar_Util.string_of_int i in
        (uu____2519, FStar_Pervasives_Native.None) in
      FStar_Const.Const_int uu____2513 in
    const_as_tm uu____2512 p in
  let bool_as_const p b = const_as_tm (FStar_Const.Const_bool b) p in
  let string_as_const p b =
    const_as_tm
      (FStar_Const.Const_string ((FStar_Util.bytes_of_string b), p)) p in
  let arg_as_int uu____2546 =
    match uu____2546 with
    | (a,uu____2551) ->
        let uu____2553 =
          let uu____2554 = FStar_Syntax_Subst.compress a in
          uu____2554.FStar_Syntax_Syntax.n in
        (match uu____2553 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (i,FStar_Pervasives_Native.None )) ->
             let uu____2564 = FStar_Util.int_of_string i in
             FStar_Pervasives_Native.Some uu____2564
         | uu____2565 -> FStar_Pervasives_Native.None) in
  let arg_as_bounded_int uu____2574 =
    match uu____2574 with
    | (a,uu____2581) ->
        let uu____2585 =
          let uu____2586 = FStar_Syntax_Subst.compress a in
          uu____2586.FStar_Syntax_Syntax.n in
        (match uu____2585 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.tk = uu____2593;
                FStar_Syntax_Syntax.pos = uu____2594;
                FStar_Syntax_Syntax.vars = uu____2595;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.tk
                                                              = uu____2597;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____2598;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____2599;_},uu____2600)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____2627 =
               let uu____2630 = FStar_Util.int_of_string i in
               (fv1, uu____2630) in
             FStar_Pervasives_Native.Some uu____2627
         | uu____2633 -> FStar_Pervasives_Native.None) in
  let arg_as_bool uu____2642 =
    match uu____2642 with
    | (a,uu____2647) ->
        let uu____2649 =
          let uu____2650 = FStar_Syntax_Subst.compress a in
          uu____2650.FStar_Syntax_Syntax.n in
        (match uu____2649 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
             FStar_Pervasives_Native.Some b
         | uu____2655 -> FStar_Pervasives_Native.None) in
  let arg_as_char uu____2662 =
    match uu____2662 with
    | (a,uu____2667) ->
        let uu____2669 =
          let uu____2670 = FStar_Syntax_Subst.compress a in
          uu____2670.FStar_Syntax_Syntax.n in
        (match uu____2669 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
             FStar_Pervasives_Native.Some c
         | uu____2675 -> FStar_Pervasives_Native.None) in
  let arg_as_string uu____2682 =
    match uu____2682 with
    | (a,uu____2687) ->
        let uu____2689 =
          let uu____2690 = FStar_Syntax_Subst.compress a in
          uu____2690.FStar_Syntax_Syntax.n in
        (match uu____2689 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (bytes,uu____2695)) ->
             FStar_Pervasives_Native.Some (FStar_Util.string_of_bytes bytes)
         | uu____2698 -> FStar_Pervasives_Native.None) in
  let arg_as_list f uu____2719 =
    match uu____2719 with
    | (a,uu____2728) ->
        let rec sequence l =
          match l with
          | [] -> FStar_Pervasives_Native.Some []
          | (FStar_Pervasives_Native.None )::uu____2745 ->
              FStar_Pervasives_Native.None
          | (FStar_Pervasives_Native.Some x)::xs ->
              let uu____2755 = sequence xs in
              (match uu____2755 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some xs' ->
                   FStar_Pervasives_Native.Some (x :: xs')) in
        let uu____2766 = FStar_Syntax_Util.list_elements a in
        (match uu____2766 with
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some elts ->
             let uu____2776 =
               FStar_List.map
                 (fun x  ->
                    let uu____2783 = FStar_Syntax_Syntax.as_arg x in
                    f uu____2783) elts in
             sequence uu____2776) in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____2813 = f a in FStar_Pervasives_Native.Some uu____2813
    | uu____2814 -> FStar_Pervasives_Native.None in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____2853 = f a0 a1 in FStar_Pervasives_Native.Some uu____2853
    | uu____2854 -> FStar_Pervasives_Native.None in
  let unary_op as_a f r args =
    let uu____2898 = FStar_List.map as_a args in lift_unary (f r) uu____2898 in
  let binary_op as_a f r args =
    let uu____2948 = FStar_List.map as_a args in lift_binary (f r) uu____2948 in
  let as_primitive_step uu____2965 =
    match uu____2965 with
    | (l,arity,f) ->
        { name = l; arity; strong_reduction_ok = true; interpretation = f } in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  -> fun x  -> let uu____3006 = f x in int_as_const r uu____3006) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  -> let uu____3033 = f x y in int_as_const r uu____3033) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  -> fun x  -> let uu____3053 = f x in bool_as_const r uu____3053) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  -> let uu____3080 = f x y in bool_as_const r uu____3080) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  -> let uu____3107 = f x y in string_as_const r uu____3107) in
  let list_of_string' rng s =
    let name l =
      let uu____3121 =
        let uu____3122 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____3122 in
      mk uu____3121 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____3132 =
      let uu____3134 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____3134 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____3132 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in int_as_const rng r in
  let string_concat' rng args =
    match args with
    | a1::a2::[] ->
        let uu____3187 = arg_as_string a1 in
        (match uu____3187 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____3191 = arg_as_list arg_as_string a2 in
             (match uu____3191 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____3199 = string_as_const rng r in
                  FStar_Pervasives_Native.Some uu____3199
              | uu____3200 -> FStar_Pervasives_Native.None)
         | uu____3203 -> FStar_Pervasives_Native.None)
    | uu____3205 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____3216 = FStar_Util.string_of_int i in
    string_as_const rng uu____3216 in
  let string_of_bool1 rng b =
    string_as_const rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____3232 = FStar_Util.string_of_int i in
    string_as_const rng uu____3232 in
  let string_of_bool2 rng b =
    string_as_const rng (if b then "true" else "false") in
  let decidable_eq neg rng args =
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) rng in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) rng in
    match args with
    | (_typ,uu____3261)::(a1,uu____3263)::(a2,uu____3265)::[] ->
        let uu____3294 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3294 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____3306 -> FStar_Pervasives_Native.None)
    | uu____3307 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____3319 =
      let uu____3329 =
        let uu____3339 =
          let uu____3349 =
            let uu____3359 =
              let uu____3369 =
                let uu____3379 =
                  let uu____3389 =
                    let uu____3399 =
                      let uu____3409 =
                        let uu____3419 =
                          let uu____3429 =
                            let uu____3439 =
                              let uu____3449 =
                                let uu____3459 =
                                  let uu____3469 =
                                    let uu____3479 =
                                      let uu____3489 =
                                        let uu____3499 =
                                          let uu____3509 =
                                            let uu____3519 =
                                              let uu____3528 =
                                                FStar_Parser_Const.p2l
                                                  ["FStar";
                                                  "String";
                                                  "list_of_string"] in
                                              (uu____3528,
                                                (Prims.parse_int "1"),
                                                (unary_op arg_as_string
                                                   list_of_string')) in
                                            let uu____3534 =
                                              let uu____3544 =
                                                let uu____3553 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "string_of_list"] in
                                                (uu____3553,
                                                  (Prims.parse_int "1"),
                                                  (unary_op
                                                     (arg_as_list arg_as_char)
                                                     string_of_list')) in
                                              let uu____3560 =
                                                let uu____3570 =
                                                  let uu____3582 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "concat"] in
                                                  (uu____3582,
                                                    (Prims.parse_int "2"),
                                                    string_concat') in
                                                [uu____3570] in
                                              uu____3544 :: uu____3560 in
                                            uu____3519 :: uu____3534 in
                                          (FStar_Parser_Const.op_notEq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq true)) ::
                                            uu____3509 in
                                        (FStar_Parser_Const.op_Eq,
                                          (Prims.parse_int "3"),
                                          (decidable_eq false)) :: uu____3499 in
                                      (FStar_Parser_Const.string_compare,
                                        (Prims.parse_int "2"),
                                        (binary_op arg_as_string
                                           string_compare'))
                                        :: uu____3489 in
                                    (FStar_Parser_Const.string_of_bool_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_bool string_of_bool2))
                                      :: uu____3479 in
                                  (FStar_Parser_Const.string_of_int_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_int string_of_int2)) ::
                                    uu____3469 in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____3459 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____3449 in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____3439 in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____3429 in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____3419 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____3409 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
                      :: uu____3399 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____3389 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____3379 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____3369 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____3359 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____3349 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____3339 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____3329 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____3319 in
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
      let uu____3999 =
        let uu____4000 =
          let uu____4001 = FStar_Syntax_Syntax.as_arg c in [uu____4001] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____4000 in
      uu____3999 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____4028 =
              let uu____4037 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____4037, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____4053  ->
                        fun uu____4054  ->
                          match (uu____4053, uu____4054) with
                          | ((int_to_t1,x),(uu____4065,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____4071 =
              let uu____4081 =
                let uu____4090 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____4090, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____4106  ->
                          fun uu____4107  ->
                            match (uu____4106, uu____4107) with
                            | ((int_to_t1,x),(uu____4118,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____4124 =
                let uu____4134 =
                  let uu____4143 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____4143, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____4159  ->
                            fun uu____4160  ->
                              match (uu____4159, uu____4160) with
                              | ((int_to_t1,x),(uu____4171,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____4134] in
              uu____4081 :: uu____4124 in
            uu____4028 :: uu____4071)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop r args =
    match args with
    | (_typ,uu____4236)::(a1,uu____4238)::(a2,uu____4240)::[] ->
        let uu____4269 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4269 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___169_4274 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___169_4274.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___169_4274.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___169_4274.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___170_4282 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___170_4282.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___170_4282.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___170_4282.FStar_Syntax_Syntax.vars)
                })
         | uu____4287 -> FStar_Pervasives_Native.None)
    | (_typ,uu____4289)::uu____4290::(a1,uu____4292)::(a2,uu____4294)::[] ->
        let uu____4331 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4331 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___169_4336 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___169_4336.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___169_4336.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___169_4336.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___170_4344 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___170_4344.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___170_4344.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___170_4344.FStar_Syntax_Syntax.vars)
                })
         | uu____4349 -> FStar_Pervasives_Native.None)
    | uu____4350 -> failwith "Unexpected number of arguments" in
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
      let uu____4362 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops cfg.steps) in
      if uu____4362
      then tm
      else
        (let uu____4364 = FStar_Syntax_Util.head_and_args tm in
         match uu____4364 with
         | (head1,args) ->
             let uu____4390 =
               let uu____4391 = FStar_Syntax_Util.un_uinst head1 in
               uu____4391.FStar_Syntax_Syntax.n in
             (match uu____4390 with
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____4395 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps in
                  (match uu____4395 with
                   | FStar_Pervasives_Native.None  -> tm
                   | FStar_Pervasives_Native.Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then tm
                       else
                         (let uu____4411 =
                            prim_step.interpretation
                              head1.FStar_Syntax_Syntax.pos args in
                          match uu____4411 with
                          | FStar_Pervasives_Native.None  -> tm
                          | FStar_Pervasives_Native.Some reduced -> reduced))
              | uu____4414 -> tm))
let reduce_equality:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___171_4425 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___171_4425.tcenv);
           delta_level = (uu___171_4425.delta_level);
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
        let uu___172_4449 = t in
        {
          FStar_Syntax_Syntax.n = (uu___172_4449.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___172_4449.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___172_4449.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid ->
            FStar_Pervasives_Native.Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid ->
            FStar_Pervasives_Native.Some false
        | uu____4468 -> FStar_Pervasives_Native.None in
      let simplify arg = ((simp_t (FStar_Pervasives_Native.fst arg)), arg) in
      let tm1 = reduce_primops cfg tm in
      let uu____4496 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps) in
      if uu____4496
      then tm1
      else
        (match tm1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.tk = uu____4499;
                     FStar_Syntax_Syntax.pos = uu____4500;
                     FStar_Syntax_Syntax.vars = uu____4501;_},uu____4502);
                FStar_Syntax_Syntax.tk = uu____4503;
                FStar_Syntax_Syntax.pos = uu____4504;
                FStar_Syntax_Syntax.vars = uu____4505;_},args)
             ->
             let uu____4525 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
             if uu____4525
             then
               let uu____4526 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____4526 with
                | (FStar_Pervasives_Native.Some (true ),uu____4559)::
                    (uu____4560,(arg,uu____4562))::[] -> arg
                | (uu____4603,(arg,uu____4605))::(FStar_Pervasives_Native.Some
                                                  (true ),uu____4606)::[]
                    -> arg
                | (FStar_Pervasives_Native.Some (false ),uu____4647)::uu____4648::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____4686::(FStar_Pervasives_Native.Some (false
                               ),uu____4687)::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____4725 -> tm1)
             else
               (let uu____4735 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
                if uu____4735
                then
                  let uu____4736 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____4736 with
                  | (FStar_Pervasives_Native.Some (true ),uu____4769)::uu____4770::[]
                      -> w FStar_Syntax_Util.t_true
                  | uu____4808::(FStar_Pervasives_Native.Some (true
                                 ),uu____4809)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____4847)::
                      (uu____4848,(arg,uu____4850))::[] -> arg
                  | (uu____4891,(arg,uu____4893))::(FStar_Pervasives_Native.Some
                                                    (false ),uu____4894)::[]
                      -> arg
                  | uu____4935 -> tm1
                else
                  (let uu____4945 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.imp_lid in
                   if uu____4945
                   then
                     let uu____4946 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____4946 with
                     | uu____4979::(FStar_Pervasives_Native.Some (true
                                    ),uu____4980)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____5018)::uu____5019::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____5057)::
                         (uu____5058,(arg,uu____5060))::[] -> arg
                     | (uu____5101,(p,uu____5103))::(uu____5104,(q,uu____5106))::[]
                         ->
                         let uu____5148 = FStar_Syntax_Util.term_eq p q in
                         (if uu____5148
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____5150 -> tm1
                   else
                     (let uu____5160 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____5160
                      then
                        let uu____5161 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____5161 with
                        | (FStar_Pervasives_Native.Some (true ),uu____5194)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____5218)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____5242 -> tm1
                      else
                        (let uu____5252 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____5252
                         then
                           match args with
                           | (t,uu____5254)::[] ->
                               let uu____5267 =
                                 let uu____5268 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5268.FStar_Syntax_Syntax.n in
                               (match uu____5267 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5271::[],body,uu____5273) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____5289 -> tm1)
                                | uu____5291 -> tm1)
                           | (uu____5292,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____5293))::
                               (t,uu____5295)::[] ->
                               let uu____5322 =
                                 let uu____5323 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5323.FStar_Syntax_Syntax.n in
                               (match uu____5322 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5326::[],body,uu____5328) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____5344 -> tm1)
                                | uu____5346 -> tm1)
                           | uu____5347 -> tm1
                         else
                           (let uu____5354 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____5354
                            then
                              match args with
                              | (t,uu____5356)::[] ->
                                  let uu____5369 =
                                    let uu____5370 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5370.FStar_Syntax_Syntax.n in
                                  (match uu____5369 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5373::[],body,uu____5375) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____5391 -> tm1)
                                   | uu____5393 -> tm1)
                              | (uu____5394,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____5395))::
                                  (t,uu____5397)::[] ->
                                  let uu____5424 =
                                    let uu____5425 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5425.FStar_Syntax_Syntax.n in
                                  (match uu____5424 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5428::[],body,uu____5430) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____5446 -> tm1)
                                   | uu____5448 -> tm1)
                              | uu____5449 -> tm1
                            else reduce_equality cfg tm1)))))
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                FStar_Syntax_Syntax.tk = uu____5457;
                FStar_Syntax_Syntax.pos = uu____5458;
                FStar_Syntax_Syntax.vars = uu____5459;_},args)
             ->
             let uu____5475 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
             if uu____5475
             then
               let uu____5476 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____5476 with
                | (FStar_Pervasives_Native.Some (true ),uu____5509)::
                    (uu____5510,(arg,uu____5512))::[] -> arg
                | (uu____5553,(arg,uu____5555))::(FStar_Pervasives_Native.Some
                                                  (true ),uu____5556)::[]
                    -> arg
                | (FStar_Pervasives_Native.Some (false ),uu____5597)::uu____5598::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____5636::(FStar_Pervasives_Native.Some (false
                               ),uu____5637)::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____5675 -> tm1)
             else
               (let uu____5685 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
                if uu____5685
                then
                  let uu____5686 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____5686 with
                  | (FStar_Pervasives_Native.Some (true ),uu____5719)::uu____5720::[]
                      -> w FStar_Syntax_Util.t_true
                  | uu____5758::(FStar_Pervasives_Native.Some (true
                                 ),uu____5759)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____5797)::
                      (uu____5798,(arg,uu____5800))::[] -> arg
                  | (uu____5841,(arg,uu____5843))::(FStar_Pervasives_Native.Some
                                                    (false ),uu____5844)::[]
                      -> arg
                  | uu____5885 -> tm1
                else
                  (let uu____5895 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.imp_lid in
                   if uu____5895
                   then
                     let uu____5896 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____5896 with
                     | uu____5929::(FStar_Pervasives_Native.Some (true
                                    ),uu____5930)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____5968)::uu____5969::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____6007)::
                         (uu____6008,(arg,uu____6010))::[] -> arg
                     | (uu____6051,(p,uu____6053))::(uu____6054,(q,uu____6056))::[]
                         ->
                         let uu____6098 = FStar_Syntax_Util.term_eq p q in
                         (if uu____6098
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____6100 -> tm1
                   else
                     (let uu____6110 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____6110
                      then
                        let uu____6111 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____6111 with
                        | (FStar_Pervasives_Native.Some (true ),uu____6144)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____6168)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____6192 -> tm1
                      else
                        (let uu____6202 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____6202
                         then
                           match args with
                           | (t,uu____6204)::[] ->
                               let uu____6217 =
                                 let uu____6218 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____6218.FStar_Syntax_Syntax.n in
                               (match uu____6217 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____6221::[],body,uu____6223) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____6239 -> tm1)
                                | uu____6241 -> tm1)
                           | (uu____6242,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____6243))::
                               (t,uu____6245)::[] ->
                               let uu____6272 =
                                 let uu____6273 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____6273.FStar_Syntax_Syntax.n in
                               (match uu____6272 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____6276::[],body,uu____6278) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____6294 -> tm1)
                                | uu____6296 -> tm1)
                           | uu____6297 -> tm1
                         else
                           (let uu____6304 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____6304
                            then
                              match args with
                              | (t,uu____6306)::[] ->
                                  let uu____6319 =
                                    let uu____6320 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____6320.FStar_Syntax_Syntax.n in
                                  (match uu____6319 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6323::[],body,uu____6325) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____6341 -> tm1)
                                   | uu____6343 -> tm1)
                              | (uu____6344,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____6345))::
                                  (t,uu____6347)::[] ->
                                  let uu____6374 =
                                    let uu____6375 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____6375.FStar_Syntax_Syntax.n in
                                  (match uu____6374 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6378::[],body,uu____6380) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____6396 -> tm1)
                                   | uu____6398 -> tm1)
                              | uu____6399 -> tm1
                            else reduce_equality cfg tm1)))))
         | uu____6406 -> tm1)
let is_norm_request hd1 args =
  let uu____6424 =
    let uu____6428 =
      let uu____6429 = FStar_Syntax_Util.un_uinst hd1 in
      uu____6429.FStar_Syntax_Syntax.n in
    (uu____6428, args) in
  match uu____6424 with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6434::uu____6435::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6438::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
  | uu____6440 -> false
let get_norm_request args =
  match args with
  | uu____6462::(tm,uu____6464)::[] -> tm
  | (tm,uu____6474)::[] -> tm
  | uu____6479 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___144_6487  ->
    match uu___144_6487 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.tk = uu____6489;
           FStar_Syntax_Syntax.pos = uu____6490;
           FStar_Syntax_Syntax.vars = uu____6491;_},uu____6492,uu____6493))::uu____6494
        -> true
    | uu____6500 -> false
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
            (fun uu____6618  ->
               let uu____6619 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____6620 = FStar_Syntax_Print.term_to_string t1 in
               let uu____6621 =
                 let uu____6622 =
                   let uu____6624 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6624 in
                 stack_to_string uu____6622 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____6619
                 uu____6620 uu____6621);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____6636 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____6651 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____6662 =
                 let uu____6663 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____6664 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____6663 uu____6664 in
               failwith uu____6662
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (FStar_ST.write t1.FStar_Syntax_Syntax.tk
                  FStar_Pervasives_Native.None;
                rebuild cfg env stack1 t1)
           | FStar_Syntax_Syntax.Tm_uvar uu____6669 ->
               (FStar_ST.write t1.FStar_Syntax_Syntax.tk
                  FStar_Pervasives_Native.None;
                rebuild cfg env stack1 t1)
           | FStar_Syntax_Syntax.Tm_constant uu____6684 ->
               (FStar_ST.write t1.FStar_Syntax_Syntax.tk
                  FStar_Pervasives_Native.None;
                rebuild cfg env stack1 t1)
           | FStar_Syntax_Syntax.Tm_name uu____6689 ->
               (FStar_ST.write t1.FStar_Syntax_Syntax.tk
                  FStar_Pervasives_Native.None;
                rebuild cfg env stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6694;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____6695;_}
               ->
               (FStar_ST.write t1.FStar_Syntax_Syntax.tk
                  FStar_Pervasives_Native.None;
                rebuild cfg env stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6701;
                 FStar_Syntax_Syntax.fv_delta = uu____6702;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               ->
               (FStar_ST.write t1.FStar_Syntax_Syntax.tk
                  FStar_Pervasives_Native.None;
                rebuild cfg env stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6707;
                 FStar_Syntax_Syntax.fv_delta = uu____6708;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____6709);_}
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
                 let uu___173_6743 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.tk =
                     (uu___173_6743.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___173_6743.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___173_6743.FStar_Syntax_Syntax.vars)
                 } in
               (FStar_ST.write t2.FStar_Syntax_Syntax.tk
                  FStar_Pervasives_Native.None;
                rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____6775 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____6775) && (is_norm_request hd1 args))
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
                 let uu___174_6788 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___174_6788.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___174_6788.primitive_steps)
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
                  FStar_Syntax_Syntax.tk = uu____6793;
                  FStar_Syntax_Syntax.pos = uu____6794;
                  FStar_Syntax_Syntax.vars = uu____6795;_},a1::a2::rest)
               ->
               let uu____6829 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6829 with
                | (hd1,uu____6840) ->
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
                    (FStar_Const.Const_reflect uu____6895);
                  FStar_Syntax_Syntax.tk = uu____6896;
                  FStar_Syntax_Syntax.pos = uu____6897;
                  FStar_Syntax_Syntax.vars = uu____6898;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____6921 = FStar_List.tl stack1 in
               norm cfg env uu____6921 (FStar_Pervasives_Native.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.tk = uu____6924;
                  FStar_Syntax_Syntax.pos = uu____6925;
                  FStar_Syntax_Syntax.vars = uu____6926;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____6949 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6949 with
                | (reify_head,uu____6960) ->
                    let a1 =
                      let uu____6976 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (FStar_Pervasives_Native.fst a) in
                      FStar_Syntax_Subst.compress uu____6976 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____6979);
                            FStar_Syntax_Syntax.tk = uu____6980;
                            FStar_Syntax_Syntax.pos = uu____6981;
                            FStar_Syntax_Syntax.vars = uu____6982;_},a2::[])
                         ->
                         norm cfg env stack1 (FStar_Pervasives_Native.fst a2)
                     | uu____7007 ->
                         let stack2 =
                           (App
                              (reify_head, FStar_Pervasives_Native.None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____7015 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____7015
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____7022 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____7022
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____7025 =
                      let uu____7029 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____7029, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____7025 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___145_7039  ->
                         match uu___145_7039 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____7042 =
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
                 if uu____7042 then false else should_delta in
               if Prims.op_Negation should_delta1
               then rebuild cfg env stack1 t1
               else
                 (let r_env =
                    let uu____7046 = FStar_Syntax_Syntax.range_of_fv f in
                    FStar_TypeChecker_Env.set_range cfg.tcenv uu____7046 in
                  let uu____7047 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  match uu____7047 with
                  | FStar_Pervasives_Native.None  ->
                      (log cfg
                         (fun uu____7055  ->
                            FStar_Util.print "Tm_fvar case 2\n" []);
                       rebuild cfg env stack1 t1)
                  | FStar_Pervasives_Native.Some (us,t2) ->
                      (log cfg
                         (fun uu____7064  ->
                            let uu____7065 =
                              FStar_Syntax_Print.term_to_string t0 in
                            let uu____7066 =
                              FStar_Syntax_Print.term_to_string t2 in
                            FStar_Util.print2 ">>> Unfolded %s to %s\n"
                              uu____7065 uu____7066);
                       (let t3 =
                          let uu____7068 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 (UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant)) in
                          if uu____7068
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
                          | (UnivArgs (us',uu____7080))::stack2 ->
                              let env1 =
                                FStar_All.pipe_right us'
                                  (FStar_List.fold_left
                                     (fun env1  -> fun u  -> (Univ u) :: env1)
                                     env) in
                              norm cfg env1 stack2 t3
                          | uu____7095 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack1 t3
                          | uu____7096 ->
                              let uu____7097 =
                                let uu____7098 =
                                  FStar_Syntax_Print.lid_to_string
                                    (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                FStar_Util.format1
                                  "Impossible: missing universe instantiation on %s"
                                  uu____7098 in
                              failwith uu____7097
                        else norm cfg env stack1 t3)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____7101 = lookup_bvar env x in
               (match uu____7101 with
                | Univ uu____7102 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____7117 = FStar_ST.read r in
                      (match uu____7117 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____7139  ->
                                 let uu____7140 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____7141 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____7140
                                   uu____7141);
                            (let uu____7142 =
                               let uu____7143 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____7143.FStar_Syntax_Syntax.n in
                             match uu____7142 with
                             | FStar_Syntax_Syntax.Tm_abs uu____7146 ->
                                 norm cfg env2 stack1 t'
                             | uu____7156 -> rebuild cfg env2 stack1 t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____7179)::uu____7180 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____7185)::uu____7186 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____7192,uu____7193))::stack_rest ->
                    (match c with
                     | Univ uu____7196 -> norm cfg (c :: env) stack_rest t1
                     | uu____7197 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____7200::[] ->
                              (match lopt with
                               | FStar_Pervasives_Native.None  when
                                   FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____7210  ->
                                         let uu____7211 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____7211);
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
                                           (fun uu___146_7215  ->
                                              match uu___146_7215 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____7216 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____7220  ->
                                         let uu____7221 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____7221);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____7222 when
                                   (FStar_All.pipe_right cfg.steps
                                      (FStar_List.contains Reify))
                                     ||
                                     (FStar_All.pipe_right cfg.steps
                                        (FStar_List.contains CheckNoUvars))
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____7224 ->
                                   let cfg1 =
                                     let uu___175_7227 = cfg in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___175_7227.tcenv);
                                       delta_level =
                                         (uu___175_7227.delta_level);
                                       primitive_steps =
                                         (uu___175_7227.primitive_steps)
                                     } in
                                   let uu____7228 =
                                     closure_as_term cfg1 env t1 in
                                   rebuild cfg1 env stack1 uu____7228)
                          | uu____7229::tl1 ->
                              (log cfg
                                 (fun uu____7241  ->
                                    let uu____7242 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____7242);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___176_7263 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___176_7263.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____7278  ->
                          let uu____7279 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____7279);
                     norm cfg env stack2 t1)
                | (Debug uu____7280)::uu____7281 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7283 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7283
                    else
                      (let uu____7285 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7285 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7301  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____7311 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____7311
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____7320 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____7320)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___177_7325 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___177_7325.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___177_7325.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____7326 -> lopt in
                           (log cfg
                              (fun uu____7331  ->
                                 let uu____7332 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7332);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___178_7344 = cfg in
                               let uu____7345 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___178_7344.steps);
                                 tcenv = (uu___178_7344.tcenv);
                                 delta_level = (uu___178_7344.delta_level);
                                 primitive_steps = uu____7345
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____7351)::uu____7352 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7356 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7356
                    else
                      (let uu____7358 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7358 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7374  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____7384 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____7384
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____7393 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____7393)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___177_7398 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___177_7398.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___177_7398.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____7399 -> lopt in
                           (log cfg
                              (fun uu____7404  ->
                                 let uu____7405 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7405);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___178_7417 = cfg in
                               let uu____7418 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___178_7417.steps);
                                 tcenv = (uu___178_7417.tcenv);
                                 delta_level = (uu___178_7417.delta_level);
                                 primitive_steps = uu____7418
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____7424)::uu____7425 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7431 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7431
                    else
                      (let uu____7433 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7433 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7449  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____7459 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____7459
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____7468 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____7468)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___177_7473 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___177_7473.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___177_7473.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____7474 -> lopt in
                           (log cfg
                              (fun uu____7479  ->
                                 let uu____7480 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7480);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___178_7492 = cfg in
                               let uu____7493 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___178_7492.steps);
                                 tcenv = (uu___178_7492.tcenv);
                                 delta_level = (uu___178_7492.delta_level);
                                 primitive_steps = uu____7493
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____7499)::uu____7500 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7505 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7505
                    else
                      (let uu____7507 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7507 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7523  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____7533 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____7533
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____7542 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____7542)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___177_7547 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___177_7547.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___177_7547.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____7548 -> lopt in
                           (log cfg
                              (fun uu____7553  ->
                                 let uu____7554 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7554);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___178_7566 = cfg in
                               let uu____7567 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___178_7566.steps);
                                 tcenv = (uu___178_7566.tcenv);
                                 delta_level = (uu___178_7566.delta_level);
                                 primitive_steps = uu____7567
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____7573)::uu____7574 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7582 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7582
                    else
                      (let uu____7584 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7584 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7600  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____7610 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____7610
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____7619 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____7619)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___177_7624 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___177_7624.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___177_7624.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____7625 -> lopt in
                           (log cfg
                              (fun uu____7630  ->
                                 let uu____7631 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7631);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___178_7643 = cfg in
                               let uu____7644 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___178_7643.steps);
                                 tcenv = (uu___178_7643.tcenv);
                                 delta_level = (uu___178_7643.delta_level);
                                 primitive_steps = uu____7644
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7650 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7650
                    else
                      (let uu____7652 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7652 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7668  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____7678 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____7678
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____7687 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____7687)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___177_7692 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___177_7692.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___177_7692.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____7693 -> lopt in
                           (log cfg
                              (fun uu____7698  ->
                                 let uu____7699 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7699);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___178_7711 = cfg in
                               let uu____7712 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___178_7711.steps);
                                 tcenv = (uu___178_7711.tcenv);
                                 delta_level = (uu___178_7711.delta_level);
                                 primitive_steps = uu____7712
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
                      (fun uu____7745  ->
                         fun stack2  ->
                           match uu____7745 with
                           | (a,aq) ->
                               let uu____7753 =
                                 let uu____7754 =
                                   let uu____7758 =
                                     let uu____7759 =
                                       let uu____7769 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____7769, false) in
                                     Clos uu____7759 in
                                   (uu____7758, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____7754 in
                               uu____7753 :: stack2) args) in
               (log cfg
                  (fun uu____7793  ->
                     let uu____7794 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____7794);
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
                             ((let uu___179_7818 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___179_7818.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___179_7818.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____7819 ->
                      let uu____7822 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7822)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____7825 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____7825 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____7841 =
                          let uu____7842 =
                            let uu____7847 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___180_7849 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___180_7849.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___180_7849.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____7847) in
                          FStar_Syntax_Syntax.Tm_refine uu____7842 in
                        mk uu____7841 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____7862 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____7862
               else
                 (let uu____7864 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____7864 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____7870 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  -> fun uu____7878  -> Dummy :: env1)
                               env) in
                        norm_comp cfg uu____7870 c1 in
                      let t2 =
                        let uu____7885 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____7885 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____7928)::uu____7929 -> norm cfg env stack1 t11
                | (Arg uu____7934)::uu____7935 -> norm cfg env stack1 t11
                | (App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.tk = uu____7940;
                       FStar_Syntax_Syntax.pos = uu____7941;
                       FStar_Syntax_Syntax.vars = uu____7942;_},uu____7943,uu____7944))::uu____7945
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____7951)::uu____7952 ->
                    norm cfg env stack1 t11
                | uu____7957 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____7961  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____7974 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____7974
                        | FStar_Util.Inr c ->
                            let uu____7982 = norm_comp cfg env c in
                            FStar_Util.Inr uu____7982 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____7987 =
                        let uu____7988 =
                          let uu____7989 =
                            let uu____8007 = FStar_Syntax_Util.unascribe t12 in
                            (uu____8007, (tc1, tacopt1), l) in
                          FStar_Syntax_Syntax.Tm_ascribed uu____7989 in
                        mk uu____7988 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____7987)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____8055,{
                              FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                uu____8056;
                              FStar_Syntax_Syntax.lbunivs = uu____8057;
                              FStar_Syntax_Syntax.lbtyp = uu____8058;
                              FStar_Syntax_Syntax.lbeff = uu____8059;
                              FStar_Syntax_Syntax.lbdef = uu____8060;_}::uu____8061),uu____8062)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____8088 =
                 (let uu____8091 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____8091) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____8093 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____8093))) in
               if uu____8088
               then
                 let env1 =
                   let uu____8096 =
                     let uu____8097 =
                       let uu____8107 =
                         FStar_Util.mk_ref FStar_Pervasives_Native.None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____8107,
                         false) in
                     Clos uu____8097 in
                   uu____8096 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____8131 =
                    let uu____8134 =
                      let uu____8135 =
                        let uu____8136 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____8136
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____8135] in
                    FStar_Syntax_Subst.open_term uu____8134 body in
                  match uu____8131 with
                  | (bs,body1) ->
                      let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                      let lbname =
                        let x =
                          let uu____8146 = FStar_List.hd bs in
                          FStar_Pervasives_Native.fst uu____8146 in
                        FStar_Util.Inl
                          (let uu___181_8152 = x in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___181_8152.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___181_8152.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = ty
                           }) in
                      let lb1 =
                        let uu___182_8154 = lb in
                        let uu____8155 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = lbname;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___182_8154.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = ty;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___182_8154.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____8155
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____8167  -> Dummy :: env1)
                             env) in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let ((true ,lbs),body) when
               FStar_List.contains CompressUvars cfg.steps ->
               let uu____8182 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____8182 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____8210 =
                               let uu___183_8211 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___183_8211.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___183_8211.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____8210 in
                           let uu____8212 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____8212 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____8225 =
                                   FStar_List.map (fun uu____8228  -> Dummy)
                                     lbs1 in
                                 let uu____8229 =
                                   let uu____8231 =
                                     FStar_List.map
                                       (fun uu____8236  -> Dummy) xs1 in
                                   FStar_List.append uu____8231 env in
                                 FStar_List.append uu____8225 uu____8229 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____8244 =
                                       let uu___184_8245 = rc in
                                       let uu____8246 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___184_8245.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____8246;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___184_8245.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____8244
                                 | uu____8252 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___185_8255 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___185_8255.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___185_8255.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____8258 =
                        FStar_List.map (fun uu____8261  -> Dummy) lbs2 in
                      FStar_List.append uu____8258 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____8263 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____8263 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___186_8274 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.tk =
                               (uu___186_8274.FStar_Syntax_Syntax.tk);
                             FStar_Syntax_Syntax.pos =
                               (uu___186_8274.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___186_8274.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____8295 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____8295
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____8308 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____8339  ->
                        match uu____8339 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____8378 =
                                let uu___187_8379 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___187_8379.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___187_8379.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____8378 in
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
               (match uu____8308 with
                | (rec_env,memos,uu____8439) ->
                    let uu____8454 =
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
                             let uu____8501 =
                               let uu____8502 =
                                 let uu____8512 =
                                   FStar_Util.mk_ref
                                     FStar_Pervasives_Native.None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____8512, false) in
                               Clos uu____8502 in
                             uu____8501 :: env1)
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
                             FStar_Syntax_Syntax.tk = uu____8550;
                             FStar_Syntax_Syntax.pos = uu____8551;
                             FStar_Syntax_Syntax.vars = uu____8552;_},uu____8553,uu____8554))::uu____8555
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____8561 -> false in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____8568 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____8568
                        then
                          let uu___188_8569 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___188_8569.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps = (uu___188_8569.primitive_steps)
                          }
                        else
                          (let uu___189_8571 = cfg in
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___189_8571.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta];
                             primitive_steps =
                               (uu___189_8571.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____8573 =
                         let uu____8574 = FStar_Syntax_Subst.compress head1 in
                         uu____8574.FStar_Syntax_Syntax.n in
                       match uu____8573 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____8588 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8588 with
                            | (uu____8589,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____8593 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____8600 =
                                         let uu____8601 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____8601.FStar_Syntax_Syntax.n in
                                       match uu____8600 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____8606,uu____8607))
                                           ->
                                           let uu____8616 =
                                             let uu____8617 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____8617.FStar_Syntax_Syntax.n in
                                           (match uu____8616 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____8622,msrc,uu____8624))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____8633 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____8633
                                            | uu____8634 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____8635 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____8636 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____8636 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___190_8640 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___190_8640.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___190_8640.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___190_8640.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____8641 =
                                            FStar_List.tl stack1 in
                                          let uu____8642 =
                                            let uu____8643 =
                                              let uu____8646 =
                                                let uu____8647 =
                                                  let uu____8655 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____8655) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____8647 in
                                              FStar_Syntax_Syntax.mk
                                                uu____8646 in
                                            uu____8643
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____8641 uu____8642
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____8672 =
                                            let uu____8673 = is_return body in
                                            match uu____8673 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____8676;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____8677;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____8678;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____8683 -> false in
                                          if uu____8672
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
                                               let uu____8706 =
                                                 let uu____8709 =
                                                   let uu____8710 =
                                                     let uu____8720 =
                                                       let uu____8722 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____8722] in
                                                     (uu____8720, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc)) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____8710 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8709 in
                                               uu____8706
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____8741 =
                                                 let uu____8742 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____8742.FStar_Syntax_Syntax.n in
                                               match uu____8741 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____8748::uu____8749::[])
                                                   ->
                                                   let uu____8755 =
                                                     let uu____8758 =
                                                       let uu____8759 =
                                                         let uu____8764 =
                                                           let uu____8766 =
                                                             let uu____8767 =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____8767 in
                                                           let uu____8768 =
                                                             let uu____8770 =
                                                               let uu____8771
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____8771 in
                                                             [uu____8770] in
                                                           uu____8766 ::
                                                             uu____8768 in
                                                         (bind1, uu____8764) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____8759 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8758 in
                                                   uu____8755
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____8783 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____8789 =
                                                 let uu____8792 =
                                                   let uu____8793 =
                                                     let uu____8803 =
                                                       let uu____8805 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____8806 =
                                                         let uu____8808 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____8809 =
                                                           let uu____8811 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____8812 =
                                                             let uu____8814 =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____8815 =
                                                               let uu____8817
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____8818
                                                                 =
                                                                 let uu____8820
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____8820] in
                                                               uu____8817 ::
                                                                 uu____8818 in
                                                             uu____8814 ::
                                                               uu____8815 in
                                                           uu____8811 ::
                                                             uu____8812 in
                                                         uu____8808 ::
                                                           uu____8809 in
                                                       uu____8805 ::
                                                         uu____8806 in
                                                     (bind_inst, uu____8803) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____8793 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8792 in
                                               uu____8789
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____8832 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____8832 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____8850 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8850 with
                            | (uu____8851,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____8874 =
                                        let uu____8875 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____8875.FStar_Syntax_Syntax.n in
                                      match uu____8874 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____8881) -> t4
                                      | uu____8886 -> head2 in
                                    let uu____8887 =
                                      let uu____8888 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____8888.FStar_Syntax_Syntax.n in
                                    match uu____8887 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____8893 ->
                                        FStar_Pervasives_Native.None in
                                  let uu____8894 = maybe_extract_fv head2 in
                                  match uu____8894 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____8900 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____8900
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____8904 =
                                          maybe_extract_fv head3 in
                                        match uu____8904 with
                                        | FStar_Pervasives_Native.Some
                                            uu____8907 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____8908 ->
                                            FStar_Pervasives_Native.Some
                                              false in
                                      (head3, action_unfolded)
                                  | uu____8911 ->
                                      (head2, FStar_Pervasives_Native.None) in
                                ((let is_arg_impure uu____8922 =
                                    match uu____8922 with
                                    | (e,q) ->
                                        let uu____8927 =
                                          let uu____8928 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____8928.FStar_Syntax_Syntax.n in
                                        (match uu____8927 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____8943 -> false) in
                                  let uu____8944 =
                                    let uu____8945 =
                                      let uu____8949 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____8949 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____8945 in
                                  if uu____8944
                                  then
                                    let uu____8952 =
                                      let uu____8953 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____8953 in
                                    failwith uu____8952
                                  else ());
                                 (let uu____8955 =
                                    maybe_unfold_action head_app in
                                  match uu____8955 with
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
                                      let uu____8990 = FStar_List.tl stack1 in
                                      norm cfg env uu____8990 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____9004 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____9004 in
                           let uu____9005 = FStar_List.tl stack1 in
                           norm cfg env uu____9005 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____9086  ->
                                     match uu____9086 with
                                     | (pat,wopt,tm) ->
                                         let uu____9120 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____9120))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____9144 = FStar_List.tl stack1 in
                           norm cfg env uu____9144 tm
                       | uu____9145 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.tk = uu____9154;
                             FStar_Syntax_Syntax.pos = uu____9155;
                             FStar_Syntax_Syntax.vars = uu____9156;_},uu____9157,uu____9158))::uu____9159
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____9165 -> false in
                    if should_reify
                    then
                      let uu____9166 = FStar_List.tl stack1 in
                      let uu____9167 =
                        let uu____9168 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____9168 in
                      norm cfg env uu____9166 uu____9167
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____9171 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____9171
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___191_9177 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___191_9177.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___191_9177.primitive_steps)
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
                | uu____9179 ->
                    (match stack1 with
                     | uu____9180::uu____9181 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____9185)
                              -> norm cfg env ((Meta (m, r)) :: stack1) head1
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
                          | uu____9202 -> norm cfg env stack1 head1)
                     | [] ->
                         let head2 = norm cfg env [] head1 in
                         let m1 =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               let uu____9212 =
                                 norm_pattern_args cfg env args in
                               FStar_Syntax_Syntax.Meta_pattern uu____9212
                           | uu____9219 -> m in
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
              let uu____9231 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____9231 with
              | (uu____9232,return_repr) ->
                  let return_inst =
                    let uu____9239 =
                      let uu____9240 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____9240.FStar_Syntax_Syntax.n in
                    match uu____9239 with
                    | FStar_Syntax_Syntax.Tm_uinst (return_tm,uu____9246::[])
                        ->
                        let uu____9252 =
                          let uu____9255 =
                            let uu____9256 =
                              let uu____9261 =
                                let uu____9263 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____9263] in
                              (return_tm, uu____9261) in
                            FStar_Syntax_Syntax.Tm_uinst uu____9256 in
                          FStar_Syntax_Syntax.mk uu____9255 in
                        uu____9252 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____9275 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____9278 =
                    let uu____9281 =
                      let uu____9282 =
                        let uu____9292 =
                          let uu____9294 = FStar_Syntax_Syntax.as_arg t in
                          let uu____9295 =
                            let uu____9297 = FStar_Syntax_Syntax.as_arg e in
                            [uu____9297] in
                          uu____9294 :: uu____9295 in
                        (return_inst, uu____9292) in
                      FStar_Syntax_Syntax.Tm_app uu____9282 in
                    FStar_Syntax_Syntax.mk uu____9281 in
                  uu____9278 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____9310 = FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____9310 with
               | FStar_Pervasives_Native.None  ->
                   let uu____9312 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____9312
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____9313;
                     FStar_TypeChecker_Env.mtarget = uu____9314;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____9315;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____9326;
                     FStar_TypeChecker_Env.mtarget = uu____9327;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____9328;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____9346 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____9346)
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
                (fun uu____9380  ->
                   match uu____9380 with
                   | (a,imp) ->
                       let uu____9387 = norm cfg env [] a in
                       (uu____9387, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___192_9402 = comp1 in
            let uu____9405 =
              let uu____9406 =
                let uu____9412 = norm cfg env [] t in
                let uu____9413 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____9412, uu____9413) in
              FStar_Syntax_Syntax.Total uu____9406 in
            {
              FStar_Syntax_Syntax.n = uu____9405;
              FStar_Syntax_Syntax.tk = (uu___192_9402.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___192_9402.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___192_9402.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___193_9428 = comp1 in
            let uu____9431 =
              let uu____9432 =
                let uu____9438 = norm cfg env [] t in
                let uu____9439 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____9438, uu____9439) in
              FStar_Syntax_Syntax.GTotal uu____9432 in
            {
              FStar_Syntax_Syntax.n = uu____9431;
              FStar_Syntax_Syntax.tk = (uu___193_9428.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___193_9428.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___193_9428.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____9474  ->
                      match uu____9474 with
                      | (a,i) ->
                          let uu____9481 = norm cfg env [] a in
                          (uu____9481, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___147_9489  ->
                      match uu___147_9489 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____9493 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____9493
                      | f -> f)) in
            let uu___194_9497 = comp1 in
            let uu____9500 =
              let uu____9501 =
                let uu___195_9502 = ct in
                let uu____9503 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____9504 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____9507 = norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____9503;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___195_9502.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____9504;
                  FStar_Syntax_Syntax.effect_args = uu____9507;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____9501 in
            {
              FStar_Syntax_Syntax.n = uu____9500;
              FStar_Syntax_Syntax.tk = (uu___194_9497.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___194_9497.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___194_9497.FStar_Syntax_Syntax.vars)
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
            (let uu___196_9526 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___196_9526.tcenv);
               delta_level = (uu___196_9526.delta_level);
               primitive_steps = (uu___196_9526.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____9531 = norm1 t in
          FStar_Syntax_Util.non_informative uu____9531 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____9534 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___197_9548 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.tk = (uu___197_9548.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___197_9548.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___197_9548.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____9558 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____9558
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
                    let uu___198_9567 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___198_9567.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___198_9567.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___198_9567.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___199_9569 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___199_9569.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___199_9569.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___199_9569.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___199_9569.FStar_Syntax_Syntax.flags)
                    } in
              let uu___200_9570 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.tk =
                  (uu___200_9570.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___200_9570.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___200_9570.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____9576 -> c
and norm_binder:
  cfg ->
    env ->
      FStar_Syntax_Syntax.binder ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
          FStar_Pervasives_Native.tuple2
  =
  fun cfg  ->
    fun env  ->
      fun uu____9579  ->
        match uu____9579 with
        | (x,imp) ->
            let uu____9582 =
              let uu___201_9583 = x in
              let uu____9584 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___201_9583.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___201_9583.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____9584
              } in
            (uu____9582, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____9590 =
          FStar_List.fold_left
            (fun uu____9602  ->
               fun b  ->
                 match uu____9602 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____9590 with | (nbs,uu____9619) -> FStar_List.rev nbs
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
            let uu____9630 =
              let uu___202_9631 = rc in
              let uu____9632 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___202_9631.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____9632;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___202_9631.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____9630
        | uu____9638 -> lopt
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
              ((let uu____9648 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____9648
                then
                  let uu____9649 = FStar_Syntax_Print.term_to_string tm in
                  let uu____9650 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2 "Normalized %s to %s\n" uu____9649
                    uu____9650
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___203_9663 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___203_9663.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____9685  ->
                    let uu____9686 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____9686);
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
              let uu____9717 =
                let uu___204_9718 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___204_9718.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___204_9718.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___204_9718.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____9717
          | (Arg (Univ uu____9723,uu____9724,uu____9725))::uu____9726 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____9728,uu____9729))::uu____9730 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____9742),aq,r))::stack2 ->
              (log cfg
                 (fun uu____9760  ->
                    let uu____9761 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____9761);
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
                 (let uu____9772 = FStar_ST.read m in
                  match uu____9772 with
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
                  | FStar_Pervasives_Native.Some (uu____9798,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq)
                          FStar_Pervasives_Native.None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 =
                FStar_Syntax_Syntax.extend_app head1 (t, aq)
                  FStar_Pervasives_Native.None r in
              let uu____9820 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____9820
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____9829  ->
                    let uu____9830 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____9830);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____9835 =
                  log cfg
                    (fun uu____9840  ->
                       let uu____9841 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____9842 =
                         let uu____9843 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____9854  ->
                                   match uu____9854 with
                                   | (p,uu____9860,uu____9861) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____9843
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____9841 uu____9842);
                  (let whnf = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___148_9872  ->
                               match uu___148_9872 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____9873 -> false)) in
                     let steps' =
                       let uu____9876 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____9876
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___205_9879 = cfg in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___205_9879.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___205_9879.primitive_steps)
                     } in
                   let norm_or_whnf env2 t1 =
                     if whnf
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____9909 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____9922 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____9960  ->
                                   fun uu____9961  ->
                                     match (uu____9960, uu____9961) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____10015 = norm_pat env3 p1 in
                                         (match uu____10015 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____9922 with
                          | (pats1,env3) ->
                              ((let uu___206_10069 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.p =
                                    (uu___206_10069.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___207_10080 = x in
                           let uu____10081 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___207_10080.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___207_10080.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____10081
                           } in
                         ((let uu___208_10087 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.p =
                               (uu___208_10087.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___209_10091 = x in
                           let uu____10092 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___209_10091.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___209_10091.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____10092
                           } in
                         ((let uu___210_10098 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.p =
                               (uu___210_10098.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___211_10107 = x in
                           let uu____10108 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___211_10107.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___211_10107.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____10108
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___212_10115 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.p =
                               (uu___212_10115.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf -> branches
                     | uu____10118 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____10131 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____10131 with
                                 | (p,wopt,e) ->
                                     let uu____10147 = norm_pat env1 p in
                                     (match uu____10147 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Pervasives_Native.Some w
                                                ->
                                                let uu____10168 =
                                                  norm_or_whnf env2 w in
                                                FStar_Pervasives_Native.Some
                                                  uu____10168 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____10172 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____10172) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____10182) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____10187 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____10188;
                        FStar_Syntax_Syntax.fv_delta = uu____10189;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Data_ctor );_}
                      -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____10190;
                        FStar_Syntax_Syntax.fv_delta = uu____10191;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Record_ctor uu____10192);_}
                      -> true
                  | uu____10196 -> false in
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
                  let uu____10292 =
                    FStar_Syntax_Util.head_and_args scrutinee1 in
                  match uu____10292 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var uu____10324 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_wild uu____10326 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____10328 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee1.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____10340 ->
                                let uu____10341 =
                                  let uu____10342 = is_cons head1 in
                                  Prims.op_Negation uu____10342 in
                                FStar_Util.Inr uu____10341)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____10354 =
                             let uu____10355 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____10355.FStar_Syntax_Syntax.n in
                           (match uu____10354 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____10362 ->
                                let uu____10363 =
                                  let uu____10364 = is_cons head1 in
                                  Prims.op_Negation uu____10364 in
                                FStar_Util.Inr uu____10363))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____10395)::rest_a,(p1,uu____10398)::rest_p) ->
                      let uu____10426 = matches_pat t1 p1 in
                      (match uu____10426 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____10440 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____10511 = matches_pat scrutinee1 p1 in
                      (match uu____10511 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____10524  ->
                                 let uu____10525 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____10526 =
                                   let uu____10527 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____10527
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____10525 uu____10526);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____10539 =
                                        let uu____10540 =
                                          let uu____10550 =
                                            FStar_Util.mk_ref
                                              (FStar_Pervasives_Native.Some
                                                 ([], t1)) in
                                          ([], t1, uu____10550, false) in
                                        Clos uu____10540 in
                                      uu____10539 :: env2) env1 s in
                             let uu____10573 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____10573))) in
                let uu____10574 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____10574
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___149_10592  ->
                match uu___149_10592 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____10595 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____10599 -> d in
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
            let uu___213_10623 = config s e in
            {
              steps = (uu___213_10623.steps);
              tcenv = (uu___213_10623.tcenv);
              delta_level = (uu___213_10623.delta_level);
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
      fun t  -> let uu____10648 = config s e in norm_comp uu____10648 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____10657 = config [] env in norm_universe uu____10657 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun c  ->
      let uu____10666 = config [] env in ghost_to_pure_aux uu____10666 [] c
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
        let uu____10680 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____10680 in
      let uu____10681 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____10681
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___214_10683 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___214_10683.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___214_10683.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____10686  ->
                    let uu____10687 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____10687))
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
            ((let uu____10706 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10706);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____10719 = config [AllowUnboundUniverses] env in
          norm_comp uu____10719 [] c
        with
        | e ->
            ((let uu____10726 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10726);
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
                   let uu____10766 =
                     let uu____10767 =
                       let uu____10772 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____10772) in
                     FStar_Syntax_Syntax.Tm_refine uu____10767 in
                   mk uu____10766 t01.FStar_Syntax_Syntax.pos
               | uu____10777 -> t2)
          | uu____10778 -> t2 in
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
        let uu____10829 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____10829 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____10845 ->
                 let uu____10849 = FStar_Syntax_Util.abs_formals e in
                 (match uu____10849 with
                  | (actuals,uu____10855,uu____10856) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____10872 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____10872 with
                         | (binders,args) ->
                             let uu____10882 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____10882
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c)))))
let eta_expand:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____10893 =
        let uu____10897 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
        (uu____10897, (t.FStar_Syntax_Syntax.n)) in
      match uu____10893 with
      | (FStar_Pervasives_Native.Some sort,uu____10904) ->
          let uu____10906 = mk sort t.FStar_Syntax_Syntax.pos in
          eta_expand_with_type env t uu____10906
      | (uu____10907,FStar_Syntax_Syntax.Tm_name x) ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____10911 ->
          let uu____10915 = FStar_Syntax_Util.head_and_args t in
          (match uu____10915 with
           | (head1,args) ->
               let uu____10941 =
                 let uu____10942 = FStar_Syntax_Subst.compress head1 in
                 uu____10942.FStar_Syntax_Syntax.n in
               (match uu____10941 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____10945,thead) ->
                    let uu____10963 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____10963 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____10998 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___219_11003 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___219_11003.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___219_11003.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___219_11003.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___219_11003.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___219_11003.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___219_11003.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___219_11003.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___219_11003.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___219_11003.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___219_11003.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___219_11003.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___219_11003.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___219_11003.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___219_11003.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___219_11003.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___219_11003.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___219_11003.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___219_11003.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___219_11003.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___219_11003.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___219_11003.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___219_11003.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___219_11003.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___219_11003.FStar_TypeChecker_Env.is_native_tactic)
                                 }) t in
                            match uu____10998 with
                            | (uu____11004,ty,uu____11006) ->
                                eta_expand_with_type env t ty))
                | uu____11007 ->
                    let uu____11008 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___220_11013 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___220_11013.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___220_11013.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___220_11013.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___220_11013.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___220_11013.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___220_11013.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___220_11013.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___220_11013.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___220_11013.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___220_11013.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___220_11013.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___220_11013.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___220_11013.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___220_11013.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___220_11013.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___220_11013.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___220_11013.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___220_11013.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___220_11013.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___220_11013.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___220_11013.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___220_11013.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___220_11013.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___220_11013.FStar_TypeChecker_Env.is_native_tactic)
                         }) t in
                    (match uu____11008 with
                     | (uu____11014,ty,uu____11016) ->
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
            | (uu____11066,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____11074,FStar_Util.Inl t) ->
                let uu____11078 =
                  let uu____11081 =
                    let uu____11082 =
                      let uu____11090 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____11090) in
                    FStar_Syntax_Syntax.Tm_arrow uu____11082 in
                  FStar_Syntax_Syntax.mk uu____11081 in
                uu____11078 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____11099 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____11099 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____11116 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____11148 ->
                    let uu____11149 =
                      let uu____11154 =
                        let uu____11155 = FStar_Syntax_Subst.compress t3 in
                        uu____11155.FStar_Syntax_Syntax.n in
                      (uu____11154, tc) in
                    (match uu____11149 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____11171) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____11195) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____11221,FStar_Util.Inl uu____11222) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____11236 -> failwith "Impossible") in
              (match uu____11116 with
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
          let uu____11305 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____11305 with
          | (univ_names1,binders1,tc) ->
              let uu____11339 = FStar_Util.left tc in
              (univ_names1, binders1, uu____11339)
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
          let uu____11369 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____11369 with
          | (univ_names1,binders1,tc) ->
              let uu____11405 = FStar_Util.right tc in
              (univ_names1, binders1, uu____11405)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____11433 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____11433 with
           | (univ_names1,binders1,typ1) ->
               let uu___221_11449 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___221_11449.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___221_11449.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___221_11449.FStar_Syntax_Syntax.sigmeta)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___222_11461 = s in
          let uu____11462 =
            let uu____11463 =
              let uu____11468 = FStar_List.map (elim_uvars env) sigs in
              (uu____11468, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____11463 in
          {
            FStar_Syntax_Syntax.sigel = uu____11462;
            FStar_Syntax_Syntax.sigrng =
              (uu___222_11461.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___222_11461.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___222_11461.FStar_Syntax_Syntax.sigmeta)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____11480 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____11480 with
           | (univ_names1,uu____11490,typ1) ->
               let uu___223_11498 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___223_11498.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___223_11498.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___223_11498.FStar_Syntax_Syntax.sigmeta)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____11503 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____11503 with
           | (univ_names1,uu____11513,typ1) ->
               let uu___224_11521 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___224_11521.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___224_11521.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___224_11521.FStar_Syntax_Syntax.sigmeta)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids,attrs) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____11548 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____11548 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____11563 =
                            let uu____11564 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____11564 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____11563 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___225_11567 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___225_11567.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___225_11567.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___226_11568 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids, attrs));
            FStar_Syntax_Syntax.sigrng =
              (uu___226_11568.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___226_11568.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___226_11568.FStar_Syntax_Syntax.sigmeta)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___227_11576 = s in
          let uu____11577 =
            let uu____11578 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____11578 in
          {
            FStar_Syntax_Syntax.sigel = uu____11577;
            FStar_Syntax_Syntax.sigrng =
              (uu___227_11576.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___227_11576.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___227_11576.FStar_Syntax_Syntax.sigmeta)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____11582 = elim_uvars_aux_t env us [] t in
          (match uu____11582 with
           | (us1,uu____11592,t1) ->
               let uu___228_11600 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___228_11600.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___228_11600.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___228_11600.FStar_Syntax_Syntax.sigmeta)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11601 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____11603 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____11603 with
           | (univs1,binders,signature) ->
               let uu____11619 =
                 let uu____11624 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____11624 with
                 | (univs_opening,univs2) ->
                     let uu____11639 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____11639) in
               (match uu____11619 with
                | (univs_opening,univs_closing) ->
                    let uu____11649 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____11653 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____11654 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____11653, uu____11654) in
                    (match uu____11649 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____11673 =
                           match uu____11673 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____11686 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____11686 with
                                | (us1,t1) ->
                                    let uu____11693 =
                                      let uu____11696 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____11703 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____11696, uu____11703) in
                                    (match uu____11693 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____11714 =
                                           let uu____11717 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____11725 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____11717, uu____11725) in
                                         (match uu____11714 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____11738 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____11738 in
                                              let uu____11739 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____11739 with
                                               | (uu____11750,uu____11751,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____11760 =
                                                       let uu____11761 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____11761 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____11760 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____11766 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____11766 with
                           | (uu____11773,uu____11774,t1) -> t1 in
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
                             | uu____11821 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____11839 =
                               let uu____11840 =
                                 FStar_Syntax_Subst.compress body in
                               uu____11840.FStar_Syntax_Syntax.n in
                             match uu____11839 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____11888 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____11909 =
                               let uu____11910 =
                                 FStar_Syntax_Subst.compress t in
                               uu____11910.FStar_Syntax_Syntax.n in
                             match uu____11909 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____11925) ->
                                 let uu____11938 = destruct_action_body body in
                                 (match uu____11938 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____11972 ->
                                 let uu____11973 = destruct_action_body t in
                                 (match uu____11973 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____12009 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____12009 with
                           | (action_univs,t) ->
                               let uu____12016 = destruct_action_typ_templ t in
                               (match uu____12016 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___229_12045 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___229_12045.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___229_12045.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___230_12047 = ed in
                           let uu____12048 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____12049 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____12050 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____12051 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____12052 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____12053 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____12054 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____12055 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____12056 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____12057 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____12058 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____12059 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____12060 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____12061 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___230_12047.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___230_12047.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____12048;
                             FStar_Syntax_Syntax.bind_wp = uu____12049;
                             FStar_Syntax_Syntax.if_then_else = uu____12050;
                             FStar_Syntax_Syntax.ite_wp = uu____12051;
                             FStar_Syntax_Syntax.stronger = uu____12052;
                             FStar_Syntax_Syntax.close_wp = uu____12053;
                             FStar_Syntax_Syntax.assert_p = uu____12054;
                             FStar_Syntax_Syntax.assume_p = uu____12055;
                             FStar_Syntax_Syntax.null_wp = uu____12056;
                             FStar_Syntax_Syntax.trivial = uu____12057;
                             FStar_Syntax_Syntax.repr = uu____12058;
                             FStar_Syntax_Syntax.return_repr = uu____12059;
                             FStar_Syntax_Syntax.bind_repr = uu____12060;
                             FStar_Syntax_Syntax.actions = uu____12061
                           } in
                         let uu___231_12063 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___231_12063.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___231_12063.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___231_12063.FStar_Syntax_Syntax.sigmeta)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___150_12074 =
            match uu___150_12074 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____12089 = elim_uvars_aux_t env us [] t in
                (match uu____12089 with
                 | (us1,uu____12102,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___232_12113 = sub_eff in
            let uu____12114 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____12116 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___232_12113.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___232_12113.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____12114;
              FStar_Syntax_Syntax.lift = uu____12116
            } in
          let uu___233_12118 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___233_12118.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___233_12118.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___233_12118.FStar_Syntax_Syntax.sigmeta)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____12126 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____12126 with
           | (univ_names1,binders1,comp1) ->
               let uu___234_12148 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___234_12148.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___234_12148.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___234_12148.FStar_Syntax_Syntax.sigmeta)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____12155 -> s