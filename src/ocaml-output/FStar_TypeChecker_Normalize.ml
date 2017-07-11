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
  let uu____772 = FStar_ST.read r in
  match uu____772 with
  | FStar_Pervasives_Native.Some uu____777 ->
      failwith "Unexpected set_memo: thunk already evaluated"
  | FStar_Pervasives_Native.None  ->
      FStar_ST.write r (FStar_Pervasives_Native.Some t)
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____787 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____787 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___139_793  ->
    match uu___139_793 with
    | Arg (c,uu____795,uu____796) ->
        let uu____797 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____797
    | MemoLazy uu____798 -> "MemoLazy"
    | Abs (uu____802,bs,uu____804,uu____805,uu____806) ->
        let uu____809 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____809
    | UnivArgs uu____816 -> "UnivArgs"
    | Match uu____820 -> "Match"
    | App (t,uu____825,uu____826) ->
        let uu____827 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____827
    | Meta (m,uu____829) -> "Meta"
    | Let uu____830 -> "Let"
    | Steps (uu____835,uu____836,uu____837) -> "Steps"
    | Debug t ->
        let uu____843 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____843
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____850 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____850 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____866 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____866 then f () else ()
let is_empty uu___140_877 =
  match uu___140_877 with | [] -> true | uu____879 -> false
let lookup_bvar env x =
  try FStar_List.nth env x.FStar_Syntax_Syntax.index
  with
  | uu____904 ->
      let uu____905 =
        let uu____906 = FStar_Syntax_Print.db_to_string x in
        FStar_Util.format1 "Failed to find %s\n" uu____906 in
      failwith uu____905
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
          let uu____941 =
            FStar_List.fold_left
              (fun uu____959  ->
                 fun u1  ->
                   match uu____959 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____974 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____974 with
                        | (k_u,n1) ->
                            let uu____983 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____983
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____941 with
          | (uu____993,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____1012 = FStar_List.nth env x in
                 match uu____1012 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____1015 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____1022 ->
                   let uu____1023 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____1023
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____1027 when
              FStar_All.pipe_right cfg.steps
                (FStar_List.contains CheckNoUvars)
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1032 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1037 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1042 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____1042 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____1053 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____1053 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____1058 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____1065 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____1065 with
                                  | (uu____1068,m) -> n1 <= m)) in
                        if uu____1058 then rest1 else us1
                    | uu____1072 -> us1)
               | uu____1075 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1078 = aux u3 in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____1078 in
        let uu____1080 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____1080
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1082 = aux u in
           match uu____1082 with
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
          (fun uu____1167  ->
             let uu____1168 = FStar_Syntax_Print.tag_of_term t in
             let uu____1169 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1168
               uu____1169);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1170 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1173 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____1186 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____1187 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____1188 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____1189 ->
                  let uu____1198 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains CheckNoUvars) in
                  if uu____1198
                  then
                    let uu____1199 =
                      let uu____1200 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos in
                      let uu____1201 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____1200 uu____1201 in
                    failwith uu____1199
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____1204 =
                    let uu____1205 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____1205 in
                  mk uu____1204 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____1210 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____1210
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____1212 = lookup_bvar env x in
                  (match uu____1212 with
                   | Univ uu____1213 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____1217) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____1265 = closures_as_binders_delayed cfg env bs in
                  (match uu____1265 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____1284 =
                         let uu____1285 =
                           let uu____1294 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____1294) in
                         FStar_Syntax_Syntax.Tm_abs uu____1285 in
                       mk uu____1284 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____1311 = closures_as_binders_delayed cfg env bs in
                  (match uu____1311 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____1338 =
                    let uu____1345 =
                      let uu____1349 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____1349] in
                    closures_as_binders_delayed cfg env uu____1345 in
                  (match uu____1338 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____1362 =
                         let uu____1363 =
                           let uu____1367 =
                             let uu____1368 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____1368
                               FStar_Pervasives_Native.fst in
                           (uu____1367, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____1363 in
                       mk uu____1362 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____1417 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____1417
                    | FStar_Util.Inr c ->
                        let uu____1425 = close_comp cfg env c in
                        FStar_Util.Inr uu____1425 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____1434 =
                    let uu____1435 =
                      let uu____1449 = closure_as_term_delayed cfg env t11 in
                      (uu____1449, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____1435 in
                  mk uu____1434 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____1476 =
                    let uu____1477 =
                      let uu____1481 = closure_as_term_delayed cfg env t' in
                      let uu____1483 =
                        let uu____1484 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____1484 in
                      (uu____1481, uu____1483) in
                    FStar_Syntax_Syntax.Tm_meta uu____1477 in
                  mk uu____1476 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____1516 =
                    let uu____1517 =
                      let uu____1521 = closure_as_term_delayed cfg env t' in
                      let uu____1523 =
                        let uu____1524 =
                          let uu____1528 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____1528) in
                        FStar_Syntax_Syntax.Meta_monadic uu____1524 in
                      (uu____1521, uu____1523) in
                    FStar_Syntax_Syntax.Tm_meta uu____1517 in
                  mk uu____1516 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____1540 =
                    let uu____1541 =
                      let uu____1545 = closure_as_term_delayed cfg env t' in
                      let uu____1547 =
                        let uu____1548 =
                          let uu____1553 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____1553) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____1548 in
                      (uu____1545, uu____1547) in
                    FStar_Syntax_Syntax.Tm_meta uu____1541 in
                  mk uu____1540 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____1561 =
                    let uu____1562 =
                      let uu____1566 = closure_as_term_delayed cfg env t' in
                      (uu____1566, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____1562 in
                  mk uu____1561 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____1585  -> Dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let uu____1590 =
                    let uu____1596 = FStar_Syntax_Syntax.is_top_level [lb] in
                    if uu____1596
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       let uu____1607 =
                         closure_as_term cfg (Dummy :: env0) body in
                       ((FStar_Util.Inl
                           (let uu___155_1611 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___155_1611.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___155_1611.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____1607)) in
                  (match uu____1590 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___156_1621 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___156_1621.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___156_1621.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         } in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____1627,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____1651  -> fun env2  -> Dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____1656 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____1656
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____1662  -> fun env2  -> Dummy :: env2) lbs
                          env_univs in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let nm =
                      let uu____1669 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____1669
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         FStar_All.pipe_right
                           (let uu___157_1677 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___157_1677.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___157_1677.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41)) in
                    let uu___158_1678 = lb in
                    let uu____1679 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___158_1678.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___158_1678.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____1679
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____1691  -> fun env1  -> Dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____1736 =
                    match uu____1736 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____1774 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____1787 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____1825  ->
                                        fun uu____1826  ->
                                          match (uu____1825, uu____1826) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____1880 =
                                                norm_pat env3 p1 in
                                              (match uu____1880 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____1787 with
                               | (pats1,env3) ->
                                   ((let uu___159_1934 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___159_1934.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___160_1945 = x in
                                let uu____1946 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___160_1945.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___160_1945.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1946
                                } in
                              ((let uu___161_1951 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___161_1951.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___162_1955 = x in
                                let uu____1956 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___162_1955.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___162_1955.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1956
                                } in
                              ((let uu___163_1961 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___163_1961.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___164_1968 = x in
                                let uu____1969 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___164_1968.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___164_1968.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1969
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___165_1975 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___165_1975.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____1977 = norm_pat env1 pat in
                        (match uu____1977 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____1997 =
                                     closure_as_term cfg env2 w in
                                   FStar_Pervasives_Native.Some uu____1997 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____2001 =
                    let uu____2002 =
                      let uu____2014 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____2014) in
                    FStar_Syntax_Syntax.Tm_match uu____2002 in
                  mk uu____2001 t1.FStar_Syntax_Syntax.pos))
and closure_as_term_delayed:
  cfg ->
    closure Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun t  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains CompressUvars cfg.steps)
            -> t
        | uu____2057 -> closure_as_term cfg env t
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
        | uu____2071 ->
            FStar_List.map
              (fun uu____2083  ->
                 match uu____2083 with
                 | (x,imp) ->
                     let uu____2094 = closure_as_term_delayed cfg env x in
                     (uu____2094, imp)) args
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
        let uu____2104 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____2136  ->
                  fun uu____2137  ->
                    match (uu____2136, uu____2137) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___166_2181 = b in
                          let uu____2182 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___166_2181.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___166_2181.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____2182
                          } in
                        let env2 = Dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____2104 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____2226 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____2235 = closure_as_term_delayed cfg env t in
                 let uu____2236 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____2235 uu____2236
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____2244 = closure_as_term_delayed cfg env t in
                 let uu____2245 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____2244 uu____2245
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
                        (fun uu___141_2262  ->
                           match uu___141_2262 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____2265 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____2265
                           | f -> f)) in
                 let uu____2268 =
                   let uu___167_2269 = c1 in
                   let uu____2270 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____2270;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___167_2269.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____2268)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags  ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___142_2277  ->
            match uu___142_2277 with
            | FStar_Syntax_Syntax.DECREASES uu____2278 -> false
            | uu____2280 -> true))
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
                   (fun uu___143_2294  ->
                      match uu___143_2294 with
                      | FStar_Syntax_Syntax.DECREASES uu____2295 -> false
                      | uu____2297 -> true)) in
            let rc1 =
              let uu___168_2299 = rc in
              let uu____2300 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___168_2299.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____2300;
                FStar_Syntax_Syntax.residual_flags = flags
              } in
            FStar_Pervasives_Native.Some rc1
        | uu____2304 -> lopt
let built_in_primitive_steps: primitive_step Prims.list =
  let const_as_tm c p = mk (FStar_Syntax_Syntax.Tm_constant c) p in
  let int_as_const p i =
    let uu____2322 =
      let uu____2323 =
        let uu____2329 = FStar_Util.string_of_int i in
        (uu____2329, FStar_Pervasives_Native.None) in
      FStar_Const.Const_int uu____2323 in
    const_as_tm uu____2322 p in
  let bool_as_const p b = const_as_tm (FStar_Const.Const_bool b) p in
  let string_as_const p b =
    const_as_tm
      (FStar_Const.Const_string ((FStar_Util.bytes_of_string b), p)) p in
  let arg_as_int uu____2356 =
    match uu____2356 with
    | (a,uu____2361) ->
        let uu____2363 =
          let uu____2364 = FStar_Syntax_Subst.compress a in
          uu____2364.FStar_Syntax_Syntax.n in
        (match uu____2363 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (i,FStar_Pervasives_Native.None )) ->
             let uu____2373 = FStar_Util.int_of_string i in
             FStar_Pervasives_Native.Some uu____2373
         | uu____2374 -> FStar_Pervasives_Native.None) in
  let arg_as_bounded_int uu____2383 =
    match uu____2383 with
    | (a,uu____2390) ->
        let uu____2394 =
          let uu____2395 = FStar_Syntax_Subst.compress a in
          uu____2395.FStar_Syntax_Syntax.n in
        (match uu____2394 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____2401;
                FStar_Syntax_Syntax.vars = uu____2402;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____2404;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____2405;_},uu____2406)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____2426 =
               let uu____2429 = FStar_Util.int_of_string i in
               (fv1, uu____2429) in
             FStar_Pervasives_Native.Some uu____2426
         | uu____2432 -> FStar_Pervasives_Native.None) in
  let arg_as_bool uu____2441 =
    match uu____2441 with
    | (a,uu____2446) ->
        let uu____2448 =
          let uu____2449 = FStar_Syntax_Subst.compress a in
          uu____2449.FStar_Syntax_Syntax.n in
        (match uu____2448 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
             FStar_Pervasives_Native.Some b
         | uu____2453 -> FStar_Pervasives_Native.None) in
  let arg_as_char uu____2460 =
    match uu____2460 with
    | (a,uu____2465) ->
        let uu____2467 =
          let uu____2468 = FStar_Syntax_Subst.compress a in
          uu____2468.FStar_Syntax_Syntax.n in
        (match uu____2467 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
             FStar_Pervasives_Native.Some c
         | uu____2472 -> FStar_Pervasives_Native.None) in
  let arg_as_string uu____2479 =
    match uu____2479 with
    | (a,uu____2484) ->
        let uu____2486 =
          let uu____2487 = FStar_Syntax_Subst.compress a in
          uu____2487.FStar_Syntax_Syntax.n in
        (match uu____2486 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (bytes,uu____2491)) ->
             FStar_Pervasives_Native.Some (FStar_Util.string_of_bytes bytes)
         | uu____2494 -> FStar_Pervasives_Native.None) in
  let arg_as_list f uu____2515 =
    match uu____2515 with
    | (a,uu____2524) ->
        let rec sequence l =
          match l with
          | [] -> FStar_Pervasives_Native.Some []
          | (FStar_Pervasives_Native.None )::uu____2541 ->
              FStar_Pervasives_Native.None
          | (FStar_Pervasives_Native.Some x)::xs ->
              let uu____2551 = sequence xs in
              (match uu____2551 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some xs' ->
                   FStar_Pervasives_Native.Some (x :: xs')) in
        let uu____2562 = FStar_Syntax_Util.list_elements a in
        (match uu____2562 with
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some elts ->
             let uu____2572 =
               FStar_List.map
                 (fun x  ->
                    let uu____2579 = FStar_Syntax_Syntax.as_arg x in
                    f uu____2579) elts in
             sequence uu____2572) in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____2609 = f a in FStar_Pervasives_Native.Some uu____2609
    | uu____2610 -> FStar_Pervasives_Native.None in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____2649 = f a0 a1 in FStar_Pervasives_Native.Some uu____2649
    | uu____2650 -> FStar_Pervasives_Native.None in
  let unary_op as_a f r args =
    let uu____2694 = FStar_List.map as_a args in lift_unary (f r) uu____2694 in
  let binary_op as_a f r args =
    let uu____2744 = FStar_List.map as_a args in lift_binary (f r) uu____2744 in
  let as_primitive_step uu____2761 =
    match uu____2761 with
    | (l,arity,f) ->
        { name = l; arity; strong_reduction_ok = true; interpretation = f } in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  -> fun x  -> let uu____2802 = f x in int_as_const r uu____2802) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2829 = f x y in int_as_const r uu____2829) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  -> fun x  -> let uu____2849 = f x in bool_as_const r uu____2849) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2876 = f x y in bool_as_const r uu____2876) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2903 = f x y in string_as_const r uu____2903) in
  let list_of_string' rng s =
    let name l =
      let uu____2916 =
        let uu____2917 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____2917 in
      mk uu____2916 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____2925 =
      let uu____2927 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____2927 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____2925 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in int_as_const rng r in
  let string_concat' rng args =
    match args with
    | a1::a2::[] ->
        let uu____2979 = arg_as_string a1 in
        (match uu____2979 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____2983 = arg_as_list arg_as_string a2 in
             (match uu____2983 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____2991 = string_as_const rng r in
                  FStar_Pervasives_Native.Some uu____2991
              | uu____2992 -> FStar_Pervasives_Native.None)
         | uu____2995 -> FStar_Pervasives_Native.None)
    | uu____2997 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____3008 = FStar_Util.string_of_int i in
    string_as_const rng uu____3008 in
  let string_of_bool1 rng b =
    string_as_const rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____3024 = FStar_Util.string_of_int i in
    string_as_const rng uu____3024 in
  let string_of_bool2 rng b =
    string_as_const rng (if b then "true" else "false") in
  let decidable_eq neg rng args =
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) rng in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) rng in
    match args with
    | (_typ,uu____3051)::(a1,uu____3053)::(a2,uu____3055)::[] ->
        let uu____3074 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3074 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____3082 -> FStar_Pervasives_Native.None)
    | uu____3083 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____3095 =
      let uu____3105 =
        let uu____3115 =
          let uu____3125 =
            let uu____3135 =
              let uu____3145 =
                let uu____3155 =
                  let uu____3165 =
                    let uu____3175 =
                      let uu____3185 =
                        let uu____3195 =
                          let uu____3205 =
                            let uu____3215 =
                              let uu____3225 =
                                let uu____3235 =
                                  let uu____3245 =
                                    let uu____3255 =
                                      let uu____3265 =
                                        let uu____3275 =
                                          let uu____3285 =
                                            let uu____3295 =
                                              let uu____3304 =
                                                FStar_Parser_Const.p2l
                                                  ["FStar";
                                                  "String";
                                                  "list_of_string"] in
                                              (uu____3304,
                                                (Prims.parse_int "1"),
                                                (unary_op arg_as_string
                                                   list_of_string')) in
                                            let uu____3310 =
                                              let uu____3320 =
                                                let uu____3329 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "string_of_list"] in
                                                (uu____3329,
                                                  (Prims.parse_int "1"),
                                                  (unary_op
                                                     (arg_as_list arg_as_char)
                                                     string_of_list')) in
                                              let uu____3336 =
                                                let uu____3346 =
                                                  let uu____3358 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "concat"] in
                                                  (uu____3358,
                                                    (Prims.parse_int "2"),
                                                    string_concat') in
                                                [uu____3346] in
                                              uu____3320 :: uu____3336 in
                                            uu____3295 :: uu____3310 in
                                          (FStar_Parser_Const.op_notEq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq true)) ::
                                            uu____3285 in
                                        (FStar_Parser_Const.op_Eq,
                                          (Prims.parse_int "3"),
                                          (decidable_eq false)) :: uu____3275 in
                                      (FStar_Parser_Const.string_compare,
                                        (Prims.parse_int "2"),
                                        (binary_op arg_as_string
                                           string_compare'))
                                        :: uu____3265 in
                                    (FStar_Parser_Const.string_of_bool_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_bool string_of_bool2))
                                      :: uu____3255 in
                                  (FStar_Parser_Const.string_of_int_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_int string_of_int2)) ::
                                    uu____3245 in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____3235 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____3225 in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____3215 in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____3205 in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____3195 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____3185 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
                      :: uu____3175 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____3165 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____3155 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____3145 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____3135 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____3125 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____3115 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____3105 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____3095 in
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
      let uu____3774 =
        let uu____3775 =
          let uu____3776 = FStar_Syntax_Syntax.as_arg c in [uu____3776] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____3775 in
      uu____3774 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____3803 =
              let uu____3812 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____3812, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____3828  ->
                        fun uu____3829  ->
                          match (uu____3828, uu____3829) with
                          | ((int_to_t1,x),(uu____3840,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____3846 =
              let uu____3856 =
                let uu____3865 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____3865, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____3881  ->
                          fun uu____3882  ->
                            match (uu____3881, uu____3882) with
                            | ((int_to_t1,x),(uu____3893,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____3899 =
                let uu____3909 =
                  let uu____3918 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____3918, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____3934  ->
                            fun uu____3935  ->
                              match (uu____3934, uu____3935) with
                              | ((int_to_t1,x),(uu____3946,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____3909] in
              uu____3856 :: uu____3899 in
            uu____3803 :: uu____3846)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop r args =
    match args with
    | (_typ,uu____4011)::(a1,uu____4013)::(a2,uu____4015)::[] ->
        let uu____4034 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4034 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___169_4038 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___169_4038.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___169_4038.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___170_4043 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___170_4043.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___170_4043.FStar_Syntax_Syntax.vars)
                })
         | uu____4046 -> FStar_Pervasives_Native.None)
    | (_typ,uu____4048)::uu____4049::(a1,uu____4051)::(a2,uu____4053)::[] ->
        let uu____4078 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4078 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___169_4082 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___169_4082.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___169_4082.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___170_4087 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___170_4087.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___170_4087.FStar_Syntax_Syntax.vars)
                })
         | uu____4090 -> FStar_Pervasives_Native.None)
    | uu____4091 -> failwith "Unexpected number of arguments" in
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
      let uu____4103 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops cfg.steps) in
      if uu____4103
      then tm
      else
        (let uu____4105 = FStar_Syntax_Util.head_and_args tm in
         match uu____4105 with
         | (head1,args) ->
             let uu____4125 =
               let uu____4126 = FStar_Syntax_Util.un_uinst head1 in
               uu____4126.FStar_Syntax_Syntax.n in
             (match uu____4125 with
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____4129 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps in
                  (match uu____4129 with
                   | FStar_Pervasives_Native.None  -> tm
                   | FStar_Pervasives_Native.Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then tm
                       else
                         (let uu____4144 =
                            prim_step.interpretation
                              head1.FStar_Syntax_Syntax.pos args in
                          match uu____4144 with
                          | FStar_Pervasives_Native.None  -> tm
                          | FStar_Pervasives_Native.Some reduced -> reduced))
              | uu____4147 -> tm))
let reduce_equality:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___171_4158 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___171_4158.tcenv);
           delta_level = (uu___171_4158.delta_level);
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
        let uu___172_4177 = t in
        {
          FStar_Syntax_Syntax.n = (uu___172_4177.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___172_4177.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid ->
            FStar_Pervasives_Native.Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid ->
            FStar_Pervasives_Native.Some false
        | uu____4191 -> FStar_Pervasives_Native.None in
      let simplify arg = ((simp_t (FStar_Pervasives_Native.fst arg)), arg) in
      let tm1 = reduce_primops cfg tm in
      let uu____4214 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps) in
      if uu____4214
      then tm1
      else
        (match tm1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.pos = uu____4217;
                     FStar_Syntax_Syntax.vars = uu____4218;_},uu____4219);
                FStar_Syntax_Syntax.pos = uu____4220;
                FStar_Syntax_Syntax.vars = uu____4221;_},args)
             ->
             let uu____4235 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
             if uu____4235
             then
               let uu____4236 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____4236 with
                | (FStar_Pervasives_Native.Some (true ),uu____4264)::
                    (uu____4265,(arg,uu____4267))::[] -> arg
                | (uu____4300,(arg,uu____4302))::(FStar_Pervasives_Native.Some
                                                  (true ),uu____4303)::[]
                    -> arg
                | (FStar_Pervasives_Native.Some (false ),uu____4336)::uu____4337::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____4369::(FStar_Pervasives_Native.Some (false
                               ),uu____4370)::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____4402 -> tm1)
             else
               (let uu____4411 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
                if uu____4411
                then
                  let uu____4412 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____4412 with
                  | (FStar_Pervasives_Native.Some (true ),uu____4440)::uu____4441::[]
                      -> w FStar_Syntax_Util.t_true
                  | uu____4473::(FStar_Pervasives_Native.Some (true
                                 ),uu____4474)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____4506)::
                      (uu____4507,(arg,uu____4509))::[] -> arg
                  | (uu____4542,(arg,uu____4544))::(FStar_Pervasives_Native.Some
                                                    (false ),uu____4545)::[]
                      -> arg
                  | uu____4578 -> tm1
                else
                  (let uu____4587 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.imp_lid in
                   if uu____4587
                   then
                     let uu____4588 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____4588 with
                     | uu____4616::(FStar_Pervasives_Native.Some (true
                                    ),uu____4617)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____4649)::uu____4650::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____4682)::
                         (uu____4683,(arg,uu____4685))::[] -> arg
                     | (uu____4718,(p,uu____4720))::(uu____4721,(q,uu____4723))::[]
                         ->
                         let uu____4756 = FStar_Syntax_Util.term_eq p q in
                         (if uu____4756
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____4758 -> tm1
                   else
                     (let uu____4767 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____4767
                      then
                        let uu____4768 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____4768 with
                        | (FStar_Pervasives_Native.Some (true ),uu____4796)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____4816)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____4836 -> tm1
                      else
                        (let uu____4845 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____4845
                         then
                           match args with
                           | (t,uu____4847)::[] ->
                               let uu____4856 =
                                 let uu____4857 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____4857.FStar_Syntax_Syntax.n in
                               (match uu____4856 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____4859::[],body,uu____4861) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____4875 -> tm1)
                                | uu____4877 -> tm1)
                           | (uu____4878,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____4879))::
                               (t,uu____4881)::[] ->
                               let uu____4901 =
                                 let uu____4902 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____4902.FStar_Syntax_Syntax.n in
                               (match uu____4901 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____4904::[],body,uu____4906) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____4920 -> tm1)
                                | uu____4922 -> tm1)
                           | uu____4923 -> tm1
                         else
                           (let uu____4929 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____4929
                            then
                              match args with
                              | (t,uu____4931)::[] ->
                                  let uu____4940 =
                                    let uu____4941 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____4941.FStar_Syntax_Syntax.n in
                                  (match uu____4940 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____4943::[],body,uu____4945) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____4959 -> tm1)
                                   | uu____4961 -> tm1)
                              | (uu____4962,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____4963))::
                                  (t,uu____4965)::[] ->
                                  let uu____4985 =
                                    let uu____4986 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____4986.FStar_Syntax_Syntax.n in
                                  (match uu____4985 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____4988::[],body,uu____4990) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____5004 -> tm1)
                                   | uu____5006 -> tm1)
                              | uu____5007 -> tm1
                            else reduce_equality cfg tm1)))))
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                FStar_Syntax_Syntax.pos = uu____5014;
                FStar_Syntax_Syntax.vars = uu____5015;_},args)
             ->
             let uu____5027 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
             if uu____5027
             then
               let uu____5028 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____5028 with
                | (FStar_Pervasives_Native.Some (true ),uu____5056)::
                    (uu____5057,(arg,uu____5059))::[] -> arg
                | (uu____5092,(arg,uu____5094))::(FStar_Pervasives_Native.Some
                                                  (true ),uu____5095)::[]
                    -> arg
                | (FStar_Pervasives_Native.Some (false ),uu____5128)::uu____5129::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____5161::(FStar_Pervasives_Native.Some (false
                               ),uu____5162)::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____5194 -> tm1)
             else
               (let uu____5203 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
                if uu____5203
                then
                  let uu____5204 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____5204 with
                  | (FStar_Pervasives_Native.Some (true ),uu____5232)::uu____5233::[]
                      -> w FStar_Syntax_Util.t_true
                  | uu____5265::(FStar_Pervasives_Native.Some (true
                                 ),uu____5266)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____5298)::
                      (uu____5299,(arg,uu____5301))::[] -> arg
                  | (uu____5334,(arg,uu____5336))::(FStar_Pervasives_Native.Some
                                                    (false ),uu____5337)::[]
                      -> arg
                  | uu____5370 -> tm1
                else
                  (let uu____5379 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.imp_lid in
                   if uu____5379
                   then
                     let uu____5380 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____5380 with
                     | uu____5408::(FStar_Pervasives_Native.Some (true
                                    ),uu____5409)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____5441)::uu____5442::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____5474)::
                         (uu____5475,(arg,uu____5477))::[] -> arg
                     | (uu____5510,(p,uu____5512))::(uu____5513,(q,uu____5515))::[]
                         ->
                         let uu____5548 = FStar_Syntax_Util.term_eq p q in
                         (if uu____5548
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____5550 -> tm1
                   else
                     (let uu____5559 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____5559
                      then
                        let uu____5560 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____5560 with
                        | (FStar_Pervasives_Native.Some (true ),uu____5588)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____5608)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____5628 -> tm1
                      else
                        (let uu____5637 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____5637
                         then
                           match args with
                           | (t,uu____5639)::[] ->
                               let uu____5648 =
                                 let uu____5649 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5649.FStar_Syntax_Syntax.n in
                               (match uu____5648 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5651::[],body,uu____5653) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____5667 -> tm1)
                                | uu____5669 -> tm1)
                           | (uu____5670,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____5671))::
                               (t,uu____5673)::[] ->
                               let uu____5693 =
                                 let uu____5694 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5694.FStar_Syntax_Syntax.n in
                               (match uu____5693 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5696::[],body,uu____5698) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____5712 -> tm1)
                                | uu____5714 -> tm1)
                           | uu____5715 -> tm1
                         else
                           (let uu____5721 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____5721
                            then
                              match args with
                              | (t,uu____5723)::[] ->
                                  let uu____5732 =
                                    let uu____5733 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5733.FStar_Syntax_Syntax.n in
                                  (match uu____5732 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5735::[],body,uu____5737) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____5751 -> tm1)
                                   | uu____5753 -> tm1)
                              | (uu____5754,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____5755))::
                                  (t,uu____5757)::[] ->
                                  let uu____5777 =
                                    let uu____5778 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5778.FStar_Syntax_Syntax.n in
                                  (match uu____5777 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5780::[],body,uu____5782) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____5796 -> tm1)
                                   | uu____5798 -> tm1)
                              | uu____5799 -> tm1
                            else reduce_equality cfg tm1)))))
         | uu____5805 -> tm1)
let is_norm_request hd1 args =
  let uu____5823 =
    let uu____5827 =
      let uu____5828 = FStar_Syntax_Util.un_uinst hd1 in
      uu____5828.FStar_Syntax_Syntax.n in
    (uu____5827, args) in
  match uu____5823 with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5832::uu____5833::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5836::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
  | uu____5838 -> false
let get_norm_request args =
  match args with
  | uu____5860::(tm,uu____5862)::[] -> tm
  | (tm,uu____5872)::[] -> tm
  | uu____5877 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___144_5885  ->
    match uu___144_5885 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.pos = uu____5887;
           FStar_Syntax_Syntax.vars = uu____5888;_},uu____5889,uu____5890))::uu____5891
        -> true
    | uu____5895 -> false
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
            (fun uu____6009  ->
               let uu____6010 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____6011 = FStar_Syntax_Print.term_to_string t1 in
               let uu____6012 =
                 let uu____6013 =
                   let uu____6015 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6015 in
                 stack_to_string uu____6013 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____6010
                 uu____6011 uu____6012);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____6027 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____6040 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____6049 =
                 let uu____6050 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____6051 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____6050 uu____6051 in
               failwith uu____6049
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____6052 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____6061 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____6062 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6063;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____6064;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6066;
                 FStar_Syntax_Syntax.fv_delta = uu____6067;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6068;
                 FStar_Syntax_Syntax.fv_delta = uu____6069;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____6070);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (FStar_Syntax_Util.is_fstar_tactics_embed hd1) ||
                 (FStar_Syntax_Util.is_fstar_tactics_by_tactic hd1)
               ->
               let args1 = closures_as_args_delayed cfg env args in
               let hd2 = closure_as_term cfg env hd1 in
               let t2 =
                 let uu___173_6094 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___173_6094.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___173_6094.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____6115 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____6115) && (is_norm_request hd1 args))
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
                 let uu___174_6125 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___174_6125.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___174_6125.primitive_steps)
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
                  FStar_Syntax_Syntax.pos = uu____6130;
                  FStar_Syntax_Syntax.vars = uu____6131;_},a1::a2::rest)
               ->
               let uu____6157 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6157 with
                | (hd1,uu____6166) ->
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
                    (FStar_Const.Const_reflect uu____6206);
                  FStar_Syntax_Syntax.pos = uu____6207;
                  FStar_Syntax_Syntax.vars = uu____6208;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____6225 = FStar_List.tl stack1 in
               norm cfg env uu____6225 (FStar_Pervasives_Native.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____6227;
                  FStar_Syntax_Syntax.vars = uu____6228;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____6245 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6245 with
                | (reify_head,uu____6254) ->
                    let a1 =
                      let uu____6266 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (FStar_Pervasives_Native.fst a) in
                      FStar_Syntax_Subst.compress uu____6266 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____6268);
                            FStar_Syntax_Syntax.pos = uu____6269;
                            FStar_Syntax_Syntax.vars = uu____6270;_},a2::[])
                         ->
                         norm cfg env stack1 (FStar_Pervasives_Native.fst a2)
                     | uu____6288 ->
                         let stack2 =
                           (App
                              (reify_head, FStar_Pervasives_Native.None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____6295 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____6295
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____6300 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____6300
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____6303 =
                      let uu____6307 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____6307, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____6303 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___145_6317  ->
                         match uu___145_6317 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____6320 =
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
                 if uu____6320 then false else should_delta in
               if Prims.op_Negation should_delta1
               then rebuild cfg env stack1 t1
               else
                 (let r_env =
                    let uu____6324 = FStar_Syntax_Syntax.range_of_fv f in
                    FStar_TypeChecker_Env.set_range cfg.tcenv uu____6324 in
                  let uu____6325 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  match uu____6325 with
                  | FStar_Pervasives_Native.None  ->
                      (log cfg
                         (fun uu____6333  ->
                            FStar_Util.print "Tm_fvar case 2\n" []);
                       rebuild cfg env stack1 t1)
                  | FStar_Pervasives_Native.Some (us,t2) ->
                      (log cfg
                         (fun uu____6342  ->
                            let uu____6343 =
                              FStar_Syntax_Print.term_to_string t0 in
                            let uu____6344 =
                              FStar_Syntax_Print.term_to_string t2 in
                            FStar_Util.print2 ">>> Unfolded %s to %s\n"
                              uu____6343 uu____6344);
                       (let t3 =
                          let uu____6346 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 (UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant)) in
                          if uu____6346
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
                          | (UnivArgs (us',uu____6358))::stack2 ->
                              let env1 =
                                FStar_All.pipe_right us'
                                  (FStar_List.fold_left
                                     (fun env1  -> fun u  -> (Univ u) :: env1)
                                     env) in
                              norm cfg env1 stack2 t3
                          | uu____6373 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack1 t3
                          | uu____6374 ->
                              let uu____6375 =
                                let uu____6376 =
                                  FStar_Syntax_Print.lid_to_string
                                    (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                FStar_Util.format1
                                  "Impossible: missing universe instantiation on %s"
                                  uu____6376 in
                              failwith uu____6375
                        else norm cfg env stack1 t3)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____6379 = lookup_bvar env x in
               (match uu____6379 with
                | Univ uu____6380 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____6395 = FStar_ST.read r in
                      (match uu____6395 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____6417  ->
                                 let uu____6418 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____6419 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____6418
                                   uu____6419);
                            (let uu____6420 =
                               let uu____6421 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____6421.FStar_Syntax_Syntax.n in
                             match uu____6420 with
                             | FStar_Syntax_Syntax.Tm_abs uu____6423 ->
                                 norm cfg env2 stack1 t'
                             | uu____6432 -> rebuild cfg env2 stack1 t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____6453)::uu____6454 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____6459)::uu____6460 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____6466,uu____6467))::stack_rest ->
                    (match c with
                     | Univ uu____6470 -> norm cfg (c :: env) stack_rest t1
                     | uu____6471 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____6474::[] ->
                              (match lopt with
                               | FStar_Pervasives_Native.None  when
                                   FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____6484  ->
                                         let uu____6485 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6485);
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
                                           (fun uu___146_6489  ->
                                              match uu___146_6489 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____6490 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____6494  ->
                                         let uu____6495 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6495);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____6496 when
                                   (FStar_All.pipe_right cfg.steps
                                      (FStar_List.contains Reify))
                                     ||
                                     (FStar_All.pipe_right cfg.steps
                                        (FStar_List.contains CheckNoUvars))
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____6498 ->
                                   let cfg1 =
                                     let uu___175_6501 = cfg in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___175_6501.tcenv);
                                       delta_level =
                                         (uu___175_6501.delta_level);
                                       primitive_steps =
                                         (uu___175_6501.primitive_steps)
                                     } in
                                   let uu____6502 =
                                     closure_as_term cfg1 env t1 in
                                   rebuild cfg1 env stack1 uu____6502)
                          | uu____6503::tl1 ->
                              (log cfg
                                 (fun uu____6515  ->
                                    let uu____6516 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____6516);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___176_6535 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___176_6535.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____6550  ->
                          let uu____6551 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____6551);
                     norm cfg env stack2 t1)
                | (Debug uu____6552)::uu____6553 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____6555 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____6555
                    else
                      (let uu____6557 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____6557 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____6573  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____6583 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____6583
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____6590 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____6590)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___177_6594 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___177_6594.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___177_6594.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____6595 -> lopt in
                           (log cfg
                              (fun uu____6600  ->
                                 let uu____6601 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____6601);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___178_6613 = cfg in
                               let uu____6614 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___178_6613.steps);
                                 tcenv = (uu___178_6613.tcenv);
                                 delta_level = (uu___178_6613.delta_level);
                                 primitive_steps = uu____6614
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____6620)::uu____6621 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____6625 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____6625
                    else
                      (let uu____6627 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____6627 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____6643  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____6653 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____6653
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____6660 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____6660)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___177_6664 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___177_6664.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___177_6664.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____6665 -> lopt in
                           (log cfg
                              (fun uu____6670  ->
                                 let uu____6671 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____6671);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___178_6683 = cfg in
                               let uu____6684 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___178_6683.steps);
                                 tcenv = (uu___178_6683.tcenv);
                                 delta_level = (uu___178_6683.delta_level);
                                 primitive_steps = uu____6684
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____6690)::uu____6691 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____6697 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____6697
                    else
                      (let uu____6699 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____6699 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____6715  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____6725 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____6725
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____6732 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____6732)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___177_6736 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___177_6736.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___177_6736.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____6737 -> lopt in
                           (log cfg
                              (fun uu____6742  ->
                                 let uu____6743 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____6743);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___178_6755 = cfg in
                               let uu____6756 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___178_6755.steps);
                                 tcenv = (uu___178_6755.tcenv);
                                 delta_level = (uu___178_6755.delta_level);
                                 primitive_steps = uu____6756
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____6762)::uu____6763 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____6768 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____6768
                    else
                      (let uu____6770 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____6770 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____6786  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____6796 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____6796
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____6803 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____6803)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___177_6807 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___177_6807.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___177_6807.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____6808 -> lopt in
                           (log cfg
                              (fun uu____6813  ->
                                 let uu____6814 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____6814);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___178_6826 = cfg in
                               let uu____6827 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___178_6826.steps);
                                 tcenv = (uu___178_6826.tcenv);
                                 delta_level = (uu___178_6826.delta_level);
                                 primitive_steps = uu____6827
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____6833)::uu____6834 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____6842 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____6842
                    else
                      (let uu____6844 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____6844 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____6860  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____6870 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____6870
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____6877 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____6877)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___177_6881 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___177_6881.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___177_6881.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____6882 -> lopt in
                           (log cfg
                              (fun uu____6887  ->
                                 let uu____6888 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____6888);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___178_6900 = cfg in
                               let uu____6901 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___178_6900.steps);
                                 tcenv = (uu___178_6900.tcenv);
                                 delta_level = (uu___178_6900.delta_level);
                                 primitive_steps = uu____6901
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____6907 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____6907
                    else
                      (let uu____6909 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____6909 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____6925  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____6935 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____6935
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____6942 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____6942)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___177_6946 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___177_6946.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___177_6946.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____6947 -> lopt in
                           (log cfg
                              (fun uu____6952  ->
                                 let uu____6953 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____6953);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___178_6965 = cfg in
                               let uu____6966 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___178_6965.steps);
                                 tcenv = (uu___178_6965.tcenv);
                                 delta_level = (uu___178_6965.delta_level);
                                 primitive_steps = uu____6966
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
                      (fun uu____6995  ->
                         fun stack2  ->
                           match uu____6995 with
                           | (a,aq) ->
                               let uu____7003 =
                                 let uu____7004 =
                                   let uu____7008 =
                                     let uu____7009 =
                                       let uu____7019 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____7019, false) in
                                     Clos uu____7009 in
                                   (uu____7008, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____7004 in
                               uu____7003 :: stack2) args) in
               (log cfg
                  (fun uu____7043  ->
                     let uu____7044 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____7044);
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
                             ((let uu___179_7063 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___179_7063.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___179_7063.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____7064 ->
                      let uu____7067 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7067)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____7070 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____7070 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____7085 =
                          let uu____7086 =
                            let uu____7090 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___180_7092 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___180_7092.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___180_7092.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____7090) in
                          FStar_Syntax_Syntax.Tm_refine uu____7086 in
                        mk uu____7085 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____7103 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____7103
               else
                 (let uu____7105 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____7105 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____7111 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  -> fun uu____7119  -> Dummy :: env1)
                               env) in
                        norm_comp cfg uu____7111 c1 in
                      let t2 =
                        let uu____7125 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____7125 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____7157)::uu____7158 -> norm cfg env stack1 t11
                | (Arg uu____7163)::uu____7164 -> norm cfg env stack1 t11
                | (App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____7169;
                       FStar_Syntax_Syntax.vars = uu____7170;_},uu____7171,uu____7172))::uu____7173
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____7177)::uu____7178 ->
                    norm cfg env stack1 t11
                | uu____7183 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____7187  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____7197 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____7197
                        | FStar_Util.Inr c ->
                            let uu____7202 = norm_comp cfg env c in
                            FStar_Util.Inr uu____7202 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____7206 =
                        let uu____7207 =
                          let uu____7208 =
                            let uu____7222 = FStar_Syntax_Util.unascribe t12 in
                            (uu____7222, (tc1, tacopt1), l) in
                          FStar_Syntax_Syntax.Tm_ascribed uu____7208 in
                        mk uu____7207 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____7206)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____7262,{
                              FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                uu____7263;
                              FStar_Syntax_Syntax.lbunivs = uu____7264;
                              FStar_Syntax_Syntax.lbtyp = uu____7265;
                              FStar_Syntax_Syntax.lbeff = uu____7266;
                              FStar_Syntax_Syntax.lbdef = uu____7267;_}::uu____7268),uu____7269)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____7289 =
                 (let uu____7292 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____7292) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____7294 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____7294))) in
               if uu____7289
               then
                 let env1 =
                   let uu____7297 =
                     let uu____7298 =
                       let uu____7308 =
                         FStar_Util.mk_ref FStar_Pervasives_Native.None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____7308,
                         false) in
                     Clos uu____7298 in
                   uu____7297 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____7331 =
                    let uu____7334 =
                      let uu____7335 =
                        let uu____7336 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____7336
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____7335] in
                    FStar_Syntax_Subst.open_term uu____7334 body in
                  match uu____7331 with
                  | (bs,body1) ->
                      let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                      let lbname =
                        let x =
                          let uu____7346 = FStar_List.hd bs in
                          FStar_Pervasives_Native.fst uu____7346 in
                        FStar_Util.Inl
                          (let uu___181_7352 = x in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___181_7352.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___181_7352.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = ty
                           }) in
                      let lb1 =
                        let uu___182_7354 = lb in
                        let uu____7355 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = lbname;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___182_7354.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = ty;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___182_7354.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____7355
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____7366  -> Dummy :: env1)
                             env) in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let ((true ,lbs),body) when
               FStar_List.contains CompressUvars cfg.steps ->
               let uu____7379 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____7379 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____7407 =
                               let uu___183_7408 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___183_7408.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___183_7408.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____7407 in
                           let uu____7409 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____7409 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____7422 =
                                   FStar_List.map (fun uu____7425  -> Dummy)
                                     lbs1 in
                                 let uu____7426 =
                                   let uu____7428 =
                                     FStar_List.map
                                       (fun uu____7433  -> Dummy) xs1 in
                                   FStar_List.append uu____7428 env in
                                 FStar_List.append uu____7422 uu____7426 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____7441 =
                                       let uu___184_7442 = rc in
                                       let uu____7443 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___184_7442.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____7443;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___184_7442.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____7441
                                 | uu____7447 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___185_7450 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___185_7450.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___185_7450.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____7453 =
                        FStar_List.map (fun uu____7456  -> Dummy) lbs2 in
                      FStar_List.append uu____7453 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____7458 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____7458 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___186_7468 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___186_7468.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___186_7468.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____7485 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____7485
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____7496 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____7527  ->
                        match uu____7527 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____7566 =
                                let uu___187_7567 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___187_7567.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___187_7567.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____7566 in
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
               (match uu____7496 with
                | (rec_env,memos,uu____7625) ->
                    let uu____7640 =
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
                             let uu____7682 =
                               let uu____7683 =
                                 let uu____7693 =
                                   FStar_Util.mk_ref
                                     FStar_Pervasives_Native.None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____7693, false) in
                               Clos uu____7683 in
                             uu____7682 :: env1)
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
                             FStar_Syntax_Syntax.pos = uu____7726;
                             FStar_Syntax_Syntax.vars = uu____7727;_},uu____7728,uu____7729))::uu____7730
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____7734 -> false in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____7741 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____7741
                        then
                          let uu___188_7742 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___188_7742.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps = (uu___188_7742.primitive_steps)
                          }
                        else
                          (let uu___189_7744 = cfg in
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___189_7744.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta];
                             primitive_steps =
                               (uu___189_7744.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____7746 =
                         let uu____7747 = FStar_Syntax_Subst.compress head1 in
                         uu____7747.FStar_Syntax_Syntax.n in
                       match uu____7746 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____7758 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____7758 with
                            | (uu____7759,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____7763 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____7770 =
                                         let uu____7771 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____7771.FStar_Syntax_Syntax.n in
                                       match uu____7770 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____7775,uu____7776))
                                           ->
                                           let uu____7781 =
                                             let uu____7782 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____7782.FStar_Syntax_Syntax.n in
                                           (match uu____7781 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____7786,msrc,uu____7788))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____7793 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____7793
                                            | uu____7794 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____7795 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____7796 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____7796 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___190_7800 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___190_7800.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___190_7800.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___190_7800.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____7801 =
                                            FStar_List.tl stack1 in
                                          let uu____7802 =
                                            let uu____7803 =
                                              let uu____7805 =
                                                let uu____7806 =
                                                  let uu____7813 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____7813) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____7806 in
                                              FStar_Syntax_Syntax.mk
                                                uu____7805 in
                                            uu____7803
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____7801 uu____7802
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____7826 =
                                            let uu____7827 = is_return body in
                                            match uu____7827 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____7830;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____7831;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____7834 -> false in
                                          if uu____7826
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
                                               let uu____7849 =
                                                 let uu____7851 =
                                                   let uu____7852 =
                                                     let uu____7861 =
                                                       let uu____7863 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____7863] in
                                                     (uu____7861, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc)) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____7852 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____7851 in
                                               uu____7849
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____7878 =
                                                 let uu____7879 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____7879.FStar_Syntax_Syntax.n in
                                               match uu____7878 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____7883::uu____7884::[])
                                                   ->
                                                   let uu____7888 =
                                                     let uu____7890 =
                                                       let uu____7891 =
                                                         let uu____7895 =
                                                           let uu____7897 =
                                                             let uu____7898 =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____7898 in
                                                           let uu____7899 =
                                                             let uu____7901 =
                                                               let uu____7902
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____7902 in
                                                             [uu____7901] in
                                                           uu____7897 ::
                                                             uu____7899 in
                                                         (bind1, uu____7895) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____7891 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____7890 in
                                                   uu____7888
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____7911 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____7915 =
                                                 let uu____7917 =
                                                   let uu____7918 =
                                                     let uu____7926 =
                                                       let uu____7928 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____7929 =
                                                         let uu____7931 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____7932 =
                                                           let uu____7934 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____7935 =
                                                             let uu____7937 =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____7938 =
                                                               let uu____7940
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____7941
                                                                 =
                                                                 let uu____7943
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____7943] in
                                                               uu____7940 ::
                                                                 uu____7941 in
                                                             uu____7937 ::
                                                               uu____7938 in
                                                           uu____7934 ::
                                                             uu____7935 in
                                                         uu____7931 ::
                                                           uu____7932 in
                                                       uu____7928 ::
                                                         uu____7929 in
                                                     (bind_inst, uu____7926) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____7918 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____7917 in
                                               uu____7915
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____7952 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____7952 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____7966 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____7966 with
                            | (uu____7967,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____7987 =
                                        let uu____7988 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____7988.FStar_Syntax_Syntax.n in
                                      match uu____7987 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____7992) -> t4
                                      | uu____7995 -> head2 in
                                    let uu____7996 =
                                      let uu____7997 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____7997.FStar_Syntax_Syntax.n in
                                    match uu____7996 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____8001 ->
                                        FStar_Pervasives_Native.None in
                                  let uu____8002 = maybe_extract_fv head2 in
                                  match uu____8002 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____8008 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____8008
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____8012 =
                                          maybe_extract_fv head3 in
                                        match uu____8012 with
                                        | FStar_Pervasives_Native.Some
                                            uu____8015 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____8016 ->
                                            FStar_Pervasives_Native.Some
                                              false in
                                      (head3, action_unfolded)
                                  | uu____8019 ->
                                      (head2, FStar_Pervasives_Native.None) in
                                ((let is_arg_impure uu____8029 =
                                    match uu____8029 with
                                    | (e,q) ->
                                        let uu____8034 =
                                          let uu____8035 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____8035.FStar_Syntax_Syntax.n in
                                        (match uu____8034 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____8045 -> false) in
                                  let uu____8046 =
                                    let uu____8047 =
                                      let uu____8051 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____8051 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____8047 in
                                  if uu____8046
                                  then
                                    let uu____8054 =
                                      let uu____8055 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____8055 in
                                    failwith uu____8054
                                  else ());
                                 (let uu____8057 =
                                    maybe_unfold_action head_app in
                                  match uu____8057 with
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
                                      let uu____8084 = FStar_List.tl stack1 in
                                      norm cfg env uu____8084 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____8094 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____8094 in
                           let uu____8095 = FStar_List.tl stack1 in
                           norm cfg env uu____8095 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____8160  ->
                                     match uu____8160 with
                                     | (pat,wopt,tm) ->
                                         let uu____8186 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____8186))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____8203 = FStar_List.tl stack1 in
                           norm cfg env uu____8203 tm
                       | uu____8204 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.pos = uu____8211;
                             FStar_Syntax_Syntax.vars = uu____8212;_},uu____8213,uu____8214))::uu____8215
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____8219 -> false in
                    if should_reify
                    then
                      let uu____8220 = FStar_List.tl stack1 in
                      let uu____8221 =
                        let uu____8222 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____8222 in
                      norm cfg env uu____8220 uu____8221
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____8225 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____8225
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___191_8231 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___191_8231.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___191_8231.primitive_steps)
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
                | uu____8233 ->
                    (match stack1 with
                     | uu____8234::uu____8235 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____8239)
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
                          | uu____8254 -> norm cfg env stack1 head1)
                     | [] ->
                         let head2 = norm cfg env [] head1 in
                         let m1 =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               let uu____8263 =
                                 norm_pattern_args cfg env args in
                               FStar_Syntax_Syntax.Meta_pattern uu____8263
                           | uu____8269 -> m in
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
              let uu____8279 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____8279 with
              | (uu____8280,return_repr) ->
                  let return_inst =
                    let uu____8286 =
                      let uu____8287 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____8287.FStar_Syntax_Syntax.n in
                    match uu____8286 with
                    | FStar_Syntax_Syntax.Tm_uinst (return_tm,uu____8291::[])
                        ->
                        let uu____8295 =
                          let uu____8297 =
                            let uu____8298 =
                              let uu____8302 =
                                let uu____8304 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____8304] in
                              (return_tm, uu____8302) in
                            FStar_Syntax_Syntax.Tm_uinst uu____8298 in
                          FStar_Syntax_Syntax.mk uu____8297 in
                        uu____8295 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____8313 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____8315 =
                    let uu____8317 =
                      let uu____8318 =
                        let uu____8326 =
                          let uu____8328 = FStar_Syntax_Syntax.as_arg t in
                          let uu____8329 =
                            let uu____8331 = FStar_Syntax_Syntax.as_arg e in
                            [uu____8331] in
                          uu____8328 :: uu____8329 in
                        (return_inst, uu____8326) in
                      FStar_Syntax_Syntax.Tm_app uu____8318 in
                    FStar_Syntax_Syntax.mk uu____8317 in
                  uu____8315 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____8341 = FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____8341 with
               | FStar_Pervasives_Native.None  ->
                   let uu____8343 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____8343
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____8344;
                     FStar_TypeChecker_Env.mtarget = uu____8345;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____8346;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____8357;
                     FStar_TypeChecker_Env.mtarget = uu____8358;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____8359;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____8377 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____8377)
and norm_pattern_args:
  cfg ->
    env ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
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
                (fun uu____8409  ->
                   match uu____8409 with
                   | (a,imp) ->
                       let uu____8416 = norm cfg env [] a in
                       (uu____8416, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___192_8428 = comp1 in
            let uu____8430 =
              let uu____8431 =
                let uu____8436 = norm cfg env [] t in
                let uu____8437 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____8436, uu____8437) in
              FStar_Syntax_Syntax.Total uu____8431 in
            {
              FStar_Syntax_Syntax.n = uu____8430;
              FStar_Syntax_Syntax.pos =
                (uu___192_8428.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___192_8428.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___193_8448 = comp1 in
            let uu____8450 =
              let uu____8451 =
                let uu____8456 = norm cfg env [] t in
                let uu____8457 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____8456, uu____8457) in
              FStar_Syntax_Syntax.GTotal uu____8451 in
            {
              FStar_Syntax_Syntax.n = uu____8450;
              FStar_Syntax_Syntax.pos =
                (uu___193_8448.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___193_8448.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____8490  ->
                      match uu____8490 with
                      | (a,i) ->
                          let uu____8497 = norm cfg env [] a in
                          (uu____8497, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___147_8505  ->
                      match uu___147_8505 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____8508 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____8508
                      | f -> f)) in
            let uu___194_8511 = comp1 in
            let uu____8513 =
              let uu____8514 =
                let uu___195_8515 = ct in
                let uu____8516 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____8517 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____8519 = norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____8516;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___195_8515.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____8517;
                  FStar_Syntax_Syntax.effect_args = uu____8519;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____8514 in
            {
              FStar_Syntax_Syntax.n = uu____8513;
              FStar_Syntax_Syntax.pos =
                (uu___194_8511.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___194_8511.FStar_Syntax_Syntax.vars)
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
            (let uu___196_8535 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___196_8535.tcenv);
               delta_level = (uu___196_8535.delta_level);
               primitive_steps = (uu___196_8535.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____8540 = norm1 t in
          FStar_Syntax_Util.non_informative uu____8540 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____8542 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___197_8553 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.pos =
                (uu___197_8553.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___197_8553.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____8560 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____8560
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
                    let uu___198_8568 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___198_8568.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___198_8568.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___198_8568.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___199_8570 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___199_8570.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___199_8570.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___199_8570.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___199_8570.FStar_Syntax_Syntax.flags)
                    } in
              let uu___200_8571 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos =
                  (uu___200_8571.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___200_8571.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____8575 -> c
and norm_binder:
  cfg ->
    env ->
      FStar_Syntax_Syntax.binder ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
          FStar_Pervasives_Native.tuple2
  =
  fun cfg  ->
    fun env  ->
      fun uu____8578  ->
        match uu____8578 with
        | (x,imp) ->
            let uu____8581 =
              let uu___201_8582 = x in
              let uu____8583 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___201_8582.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___201_8582.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____8583
              } in
            (uu____8581, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____8588 =
          FStar_List.fold_left
            (fun uu____8600  ->
               fun b  ->
                 match uu____8600 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____8588 with | (nbs,uu____8617) -> FStar_List.rev nbs
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
            let uu____8628 =
              let uu___202_8629 = rc in
              let uu____8630 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___202_8629.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____8630;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___202_8629.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____8628
        | uu____8634 -> lopt
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
              ((let uu____8644 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____8644
                then
                  let uu____8645 = FStar_Syntax_Print.term_to_string tm in
                  let uu____8646 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2 "Normalized %s to %s\n" uu____8645
                    uu____8646
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___203_8659 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___203_8659.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____8680  ->
                    let uu____8681 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____8681);
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
              let uu____8710 =
                let uu___204_8711 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___204_8711.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___204_8711.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____8710
          | (Arg (Univ uu____8714,uu____8715,uu____8716))::uu____8717 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____8719,uu____8720))::uu____8721 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____8733),aq,r))::stack2 ->
              (log cfg
                 (fun uu____8751  ->
                    let uu____8752 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____8752);
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
                 (let uu____8762 = FStar_ST.read m in
                  match uu____8762 with
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
                  | FStar_Pervasives_Native.Some (uu____8787,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq)
                          FStar_Pervasives_Native.None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 =
                FStar_Syntax_Syntax.extend_app head1 (t, aq)
                  FStar_Pervasives_Native.None r in
              let uu____8807 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____8807
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____8816  ->
                    let uu____8817 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____8817);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____8822 =
                  log cfg
                    (fun uu____8827  ->
                       let uu____8828 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____8829 =
                         let uu____8830 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____8841  ->
                                   match uu____8841 with
                                   | (p,uu____8847,uu____8848) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____8830
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____8828 uu____8829);
                  (let whnf = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___148_8859  ->
                               match uu___148_8859 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____8860 -> false)) in
                     let steps' =
                       let uu____8863 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____8863
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___205_8866 = cfg in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___205_8866.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___205_8866.primitive_steps)
                     } in
                   let norm_or_whnf env2 t1 =
                     if whnf
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____8896 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____8909 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____8947  ->
                                   fun uu____8948  ->
                                     match (uu____8947, uu____8948) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____9002 = norm_pat env3 p1 in
                                         (match uu____9002 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____8909 with
                          | (pats1,env3) ->
                              ((let uu___206_9056 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.p =
                                    (uu___206_9056.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___207_9067 = x in
                           let uu____9068 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___207_9067.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___207_9067.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9068
                           } in
                         ((let uu___208_9073 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.p =
                               (uu___208_9073.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___209_9077 = x in
                           let uu____9078 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___209_9077.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___209_9077.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9078
                           } in
                         ((let uu___210_9083 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.p =
                               (uu___210_9083.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___211_9090 = x in
                           let uu____9091 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___211_9090.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___211_9090.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9091
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___212_9097 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.p =
                               (uu___212_9097.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf -> branches
                     | uu____9100 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____9113 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____9113 with
                                 | (p,wopt,e) ->
                                     let uu____9125 = norm_pat env1 p in
                                     (match uu____9125 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Pervasives_Native.Some w
                                                ->
                                                let uu____9143 =
                                                  norm_or_whnf env2 w in
                                                FStar_Pervasives_Native.Some
                                                  uu____9143 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____9147 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____9147) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____9155) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____9158 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____9159;
                        FStar_Syntax_Syntax.fv_delta = uu____9160;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Data_ctor );_}
                      -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____9161;
                        FStar_Syntax_Syntax.fv_delta = uu____9162;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Record_ctor uu____9163);_}
                      -> true
                  | uu____9167 -> false in
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
                  let uu____9246 = FStar_Syntax_Util.head_and_args scrutinee1 in
                  match uu____9246 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var uu____9272 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_wild uu____9274 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____9276 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee1.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____9287 ->
                                let uu____9288 =
                                  let uu____9289 = is_cons head1 in
                                  Prims.op_Negation uu____9289 in
                                FStar_Util.Inr uu____9288)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____9301 =
                             let uu____9302 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____9302.FStar_Syntax_Syntax.n in
                           (match uu____9301 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____9308 ->
                                let uu____9309 =
                                  let uu____9310 = is_cons head1 in
                                  Prims.op_Negation uu____9310 in
                                FStar_Util.Inr uu____9309))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____9339)::rest_a,(p1,uu____9342)::rest_p) ->
                      let uu____9365 = matches_pat t1 p1 in
                      (match uu____9365 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____9379 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____9436 = matches_pat scrutinee1 p1 in
                      (match uu____9436 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____9449  ->
                                 let uu____9450 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____9451 =
                                   let uu____9452 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____9452
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____9450 uu____9451);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____9464 =
                                        let uu____9465 =
                                          let uu____9475 =
                                            FStar_Util.mk_ref
                                              (FStar_Pervasives_Native.Some
                                                 ([], t1)) in
                                          ([], t1, uu____9475, false) in
                                        Clos uu____9465 in
                                      uu____9464 :: env2) env1 s in
                             let uu____9498 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____9498))) in
                let uu____9499 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____9499
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___149_9517  ->
                match uu___149_9517 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____9520 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____9524 -> d in
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
            let uu___213_9548 = config s e in
            {
              steps = (uu___213_9548.steps);
              tcenv = (uu___213_9548.tcenv);
              delta_level = (uu___213_9548.delta_level);
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
      fun t  -> let uu____9573 = config s e in norm_comp uu____9573 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  -> let uu____9582 = config [] env in norm_universe uu____9582 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun c  ->
      let uu____9591 = config [] env in ghost_to_pure_aux uu____9591 [] c
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
        let uu____9605 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____9605 in
      let uu____9606 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____9606
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___214_9608 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___214_9608.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___214_9608.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____9611  ->
                    let uu____9612 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____9612))
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
            ((let uu____9631 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____9631);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____9644 = config [AllowUnboundUniverses] env in
          norm_comp uu____9644 [] c
        with
        | e ->
            ((let uu____9651 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____9651);
             c) in
      FStar_Syntax_Print.comp_to_string c1
let normalize_refinement:
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
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
                   let uu____9683 =
                     let uu____9684 =
                       let uu____9688 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____9688) in
                     FStar_Syntax_Syntax.Tm_refine uu____9684 in
                   mk uu____9683 t01.FStar_Syntax_Syntax.pos
               | uu____9691 -> t2)
          | uu____9692 -> t2 in
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
        let uu____9743 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____9743 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____9759 ->
                 let uu____9763 = FStar_Syntax_Util.abs_formals e in
                 (match uu____9763 with
                  | (actuals,uu____9769,uu____9770) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____9786 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____9786 with
                         | (binders,args) ->
                             let uu____9796 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____9796
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
      | uu____9808 ->
          let uu____9809 = FStar_Syntax_Util.head_and_args t in
          (match uu____9809 with
           | (head1,args) ->
               let uu____9829 =
                 let uu____9830 = FStar_Syntax_Subst.compress head1 in
                 uu____9830.FStar_Syntax_Syntax.n in
               (match uu____9829 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____9832,thead) ->
                    let uu____9846 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____9846 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____9877 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___219_9882 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___219_9882.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___219_9882.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___219_9882.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___219_9882.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___219_9882.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___219_9882.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___219_9882.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___219_9882.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___219_9882.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___219_9882.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___219_9882.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___219_9882.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___219_9882.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___219_9882.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___219_9882.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___219_9882.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___219_9882.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___219_9882.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___219_9882.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___219_9882.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___219_9882.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___219_9882.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___219_9882.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___219_9882.FStar_TypeChecker_Env.is_native_tactic)
                                 }) t in
                            match uu____9877 with
                            | (uu____9883,ty,uu____9885) ->
                                eta_expand_with_type env t ty))
                | uu____9886 ->
                    let uu____9887 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___220_9892 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___220_9892.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___220_9892.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___220_9892.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___220_9892.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___220_9892.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___220_9892.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___220_9892.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___220_9892.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___220_9892.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___220_9892.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___220_9892.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___220_9892.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___220_9892.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___220_9892.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___220_9892.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___220_9892.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___220_9892.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___220_9892.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___220_9892.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___220_9892.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___220_9892.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___220_9892.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___220_9892.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___220_9892.FStar_TypeChecker_Env.is_native_tactic)
                         }) t in
                    (match uu____9887 with
                     | (uu____9893,ty,uu____9895) ->
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
            | (uu____9944,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____9951,FStar_Util.Inl t) ->
                let uu____9955 =
                  let uu____9957 =
                    let uu____9958 =
                      let uu____9965 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____9965) in
                    FStar_Syntax_Syntax.Tm_arrow uu____9958 in
                  FStar_Syntax_Syntax.mk uu____9957 in
                uu____9955 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____9972 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____9972 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____9988 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____10016 ->
                    let uu____10017 =
                      let uu____10022 =
                        let uu____10023 = FStar_Syntax_Subst.compress t3 in
                        uu____10023.FStar_Syntax_Syntax.n in
                      (uu____10022, tc) in
                    (match uu____10017 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____10037) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____10057) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____10077,FStar_Util.Inl uu____10078) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____10090 -> failwith "Impossible") in
              (match uu____9988 with
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
          let uu____10154 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____10154 with
          | (univ_names1,binders1,tc) ->
              let uu____10185 = FStar_Util.left tc in
              (univ_names1, binders1, uu____10185)
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
          let uu____10213 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____10213 with
          | (univ_names1,binders1,tc) ->
              let uu____10245 = FStar_Util.right tc in
              (univ_names1, binders1, uu____10245)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____10270 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____10270 with
           | (univ_names1,binders1,typ1) ->
               let uu___221_10286 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___221_10286.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___221_10286.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___221_10286.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___221_10286.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___222_10298 = s in
          let uu____10299 =
            let uu____10300 =
              let uu____10305 = FStar_List.map (elim_uvars env) sigs in
              (uu____10305, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____10300 in
          {
            FStar_Syntax_Syntax.sigel = uu____10299;
            FStar_Syntax_Syntax.sigrng =
              (uu___222_10298.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___222_10298.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___222_10298.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___222_10298.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____10317 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____10317 with
           | (univ_names1,uu____10327,typ1) ->
               let uu___223_10335 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___223_10335.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___223_10335.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___223_10335.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___223_10335.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____10340 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____10340 with
           | (univ_names1,uu____10350,typ1) ->
               let uu___224_10358 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___224_10358.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___224_10358.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___224_10358.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___224_10358.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____10382 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____10382 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____10397 =
                            let uu____10398 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____10398 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____10397 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___225_10401 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___225_10401.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___225_10401.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___226_10402 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___226_10402.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___226_10402.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___226_10402.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___226_10402.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___227_10409 = s in
          let uu____10410 =
            let uu____10411 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____10411 in
          {
            FStar_Syntax_Syntax.sigel = uu____10410;
            FStar_Syntax_Syntax.sigrng =
              (uu___227_10409.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___227_10409.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___227_10409.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___227_10409.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____10415 = elim_uvars_aux_t env us [] t in
          (match uu____10415 with
           | (us1,uu____10425,t1) ->
               let uu___228_10433 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___228_10433.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___228_10433.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___228_10433.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___228_10433.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____10434 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____10436 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____10436 with
           | (univs1,binders,signature) ->
               let uu____10452 =
                 let uu____10457 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____10457 with
                 | (univs_opening,univs2) ->
                     let uu____10472 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____10472) in
               (match uu____10452 with
                | (univs_opening,univs_closing) ->
                    let uu____10482 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____10486 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____10487 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____10486, uu____10487) in
                    (match uu____10482 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____10506 =
                           match uu____10506 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____10519 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____10519 with
                                | (us1,t1) ->
                                    let uu____10526 =
                                      let uu____10529 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____10536 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____10529, uu____10536) in
                                    (match uu____10526 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____10547 =
                                           let uu____10550 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____10558 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____10550, uu____10558) in
                                         (match uu____10547 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____10571 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____10571 in
                                              let uu____10572 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____10572 with
                                               | (uu____10583,uu____10584,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____10593 =
                                                       let uu____10594 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____10594 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____10593 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____10599 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____10599 with
                           | (uu____10606,uu____10607,t1) -> t1 in
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
                             | uu____10644 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____10658 =
                               let uu____10659 =
                                 FStar_Syntax_Subst.compress body in
                               uu____10659.FStar_Syntax_Syntax.n in
                             match uu____10658 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____10690 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____10707 =
                               let uu____10708 =
                                 FStar_Syntax_Subst.compress t in
                               uu____10708.FStar_Syntax_Syntax.n in
                             match uu____10707 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____10720) ->
                                 let uu____10731 = destruct_action_body body in
                                 (match uu____10731 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____10755 ->
                                 let uu____10756 = destruct_action_body t in
                                 (match uu____10756 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____10782 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____10782 with
                           | (action_univs,t) ->
                               let uu____10788 = destruct_action_typ_templ t in
                               (match uu____10788 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___229_10811 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___229_10811.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___229_10811.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___230_10813 = ed in
                           let uu____10814 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____10815 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____10816 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____10817 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____10818 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____10819 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____10820 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____10821 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____10822 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____10823 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____10824 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____10825 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____10826 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____10827 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___230_10813.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___230_10813.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____10814;
                             FStar_Syntax_Syntax.bind_wp = uu____10815;
                             FStar_Syntax_Syntax.if_then_else = uu____10816;
                             FStar_Syntax_Syntax.ite_wp = uu____10817;
                             FStar_Syntax_Syntax.stronger = uu____10818;
                             FStar_Syntax_Syntax.close_wp = uu____10819;
                             FStar_Syntax_Syntax.assert_p = uu____10820;
                             FStar_Syntax_Syntax.assume_p = uu____10821;
                             FStar_Syntax_Syntax.null_wp = uu____10822;
                             FStar_Syntax_Syntax.trivial = uu____10823;
                             FStar_Syntax_Syntax.repr = uu____10824;
                             FStar_Syntax_Syntax.return_repr = uu____10825;
                             FStar_Syntax_Syntax.bind_repr = uu____10826;
                             FStar_Syntax_Syntax.actions = uu____10827
                           } in
                         let uu___231_10829 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___231_10829.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___231_10829.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___231_10829.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___231_10829.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___150_10840 =
            match uu___150_10840 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____10855 = elim_uvars_aux_t env us [] t in
                (match uu____10855 with
                 | (us1,uu____10868,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___232_10879 = sub_eff in
            let uu____10880 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____10882 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___232_10879.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___232_10879.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____10880;
              FStar_Syntax_Syntax.lift = uu____10882
            } in
          let uu___233_10884 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___233_10884.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___233_10884.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___233_10884.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___233_10884.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____10892 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____10892 with
           | (univ_names1,binders1,comp1) ->
               let uu___234_10911 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___234_10911.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___234_10911.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___234_10911.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___234_10911.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____10917 -> s