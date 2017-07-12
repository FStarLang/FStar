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
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r in
  let range_of1 uu____3051 args =
    match args with
    | uu____3058::(t,uu____3060)::[] ->
        let uu____3075 = term_of_range t.FStar_Syntax_Syntax.pos in
        FStar_Pervasives_Native.Some uu____3075
    | uu____3078 -> FStar_Pervasives_Native.None in
  let set_range_of1 r args =
    match args with
    | uu____3101::(t,uu____3103)::({
                                     FStar_Syntax_Syntax.n =
                                       FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_range r1);
                                     FStar_Syntax_Syntax.pos = uu____3105;
                                     FStar_Syntax_Syntax.vars = uu____3106;_},uu____3107)::[]
        ->
        FStar_Pervasives_Native.Some
          (let uu___169_3129 = t in
           {
             FStar_Syntax_Syntax.n = (uu___169_3129.FStar_Syntax_Syntax.n);
             FStar_Syntax_Syntax.pos = r1;
             FStar_Syntax_Syntax.vars =
               (uu___169_3129.FStar_Syntax_Syntax.vars)
           })
    | uu____3133 -> FStar_Pervasives_Native.None in
  let mk_range1 r args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____3180 =
          let uu____3191 = arg_as_string fn in
          let uu____3193 = arg_as_int from_line in
          let uu____3195 = arg_as_int from_col in
          let uu____3197 = arg_as_int to_line in
          let uu____3199 = arg_as_int to_col in
          (uu____3191, uu____3193, uu____3195, uu____3197, uu____3199) in
        (match uu____3180 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r1 =
               let uu____3218 = FStar_Range.mk_pos from_l from_c in
               let uu____3219 = FStar_Range.mk_pos to_l to_c in
               FStar_Range.mk_range fn1 uu____3218 uu____3219 in
             let uu____3220 = term_of_range r1 in
             FStar_Pervasives_Native.Some uu____3220
         | uu____3223 -> FStar_Pervasives_Native.None)
    | uu____3234 -> FStar_Pervasives_Native.None in
  let decidable_eq neg rng args =
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) rng in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) rng in
    match args with
    | (_typ,uu____3256)::(a1,uu____3258)::(a2,uu____3260)::[] ->
        let uu____3279 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3279 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____3287 -> FStar_Pervasives_Native.None)
    | uu____3288 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____3300 =
      let uu____3310 =
        let uu____3320 =
          let uu____3330 =
            let uu____3340 =
              let uu____3350 =
                let uu____3360 =
                  let uu____3370 =
                    let uu____3380 =
                      let uu____3390 =
                        let uu____3400 =
                          let uu____3410 =
                            let uu____3420 =
                              let uu____3430 =
                                let uu____3440 =
                                  let uu____3450 =
                                    let uu____3460 =
                                      let uu____3470 =
                                        let uu____3480 =
                                          let uu____3490 =
                                            let uu____3500 =
                                              let uu____3509 =
                                                FStar_Parser_Const.p2l
                                                  ["FStar";
                                                  "String";
                                                  "list_of_string"] in
                                              (uu____3509,
                                                (Prims.parse_int "1"),
                                                (unary_op arg_as_string
                                                   list_of_string')) in
                                            let uu____3515 =
                                              let uu____3525 =
                                                let uu____3534 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "string_of_list"] in
                                                (uu____3534,
                                                  (Prims.parse_int "1"),
                                                  (unary_op
                                                     (arg_as_list arg_as_char)
                                                     string_of_list')) in
                                              let uu____3541 =
                                                let uu____3551 =
                                                  let uu____3563 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "concat"] in
                                                  (uu____3563,
                                                    (Prims.parse_int "2"),
                                                    string_concat') in
                                                let uu____3572 =
                                                  let uu____3585 =
                                                    let uu____3598 =
                                                      FStar_Parser_Const.p2l
                                                        ["Prims"; "range_of"] in
                                                    (uu____3598,
                                                      (Prims.parse_int "2"),
                                                      range_of1) in
                                                  let uu____3608 =
                                                    let uu____3622 =
                                                      let uu____3635 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "set_range_of"] in
                                                      (uu____3635,
                                                        (Prims.parse_int "3"),
                                                        set_range_of1) in
                                                    let uu____3645 =
                                                      let uu____3659 =
                                                        let uu____3671 =
                                                          FStar_Parser_Const.p2l
                                                            ["Prims";
                                                            "mk_range"] in
                                                        (uu____3671,
                                                          (Prims.parse_int
                                                             "5"), mk_range1) in
                                                      [uu____3659] in
                                                    uu____3622 :: uu____3645 in
                                                  uu____3585 :: uu____3608 in
                                                uu____3551 :: uu____3572 in
                                              uu____3525 :: uu____3541 in
                                            uu____3500 :: uu____3515 in
                                          (FStar_Parser_Const.op_notEq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq true)) ::
                                            uu____3490 in
                                        (FStar_Parser_Const.op_Eq,
                                          (Prims.parse_int "3"),
                                          (decidable_eq false)) :: uu____3480 in
                                      (FStar_Parser_Const.string_compare,
                                        (Prims.parse_int "2"),
                                        (binary_op arg_as_string
                                           string_compare'))
                                        :: uu____3470 in
                                    (FStar_Parser_Const.string_of_bool_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_bool string_of_bool2))
                                      :: uu____3460 in
                                  (FStar_Parser_Const.string_of_int_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_int string_of_int2)) ::
                                    uu____3450 in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____3440 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____3430 in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____3420 in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____3410 in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____3400 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____3390 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
                      :: uu____3380 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____3370 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____3360 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____3350 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____3340 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____3330 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____3320 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____3310 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____3300 in
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
      let uu____4122 =
        let uu____4123 =
          let uu____4124 = FStar_Syntax_Syntax.as_arg c in [uu____4124] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____4123 in
      uu____4122 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____4151 =
              let uu____4160 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____4160, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____4176  ->
                        fun uu____4177  ->
                          match (uu____4176, uu____4177) with
                          | ((int_to_t1,x),(uu____4188,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____4194 =
              let uu____4204 =
                let uu____4213 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____4213, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____4229  ->
                          fun uu____4230  ->
                            match (uu____4229, uu____4230) with
                            | ((int_to_t1,x),(uu____4241,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____4247 =
                let uu____4257 =
                  let uu____4266 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____4266, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____4282  ->
                            fun uu____4283  ->
                              match (uu____4282, uu____4283) with
                              | ((int_to_t1,x),(uu____4294,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____4257] in
              uu____4204 :: uu____4247 in
            uu____4151 :: uu____4194)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop r args =
    match args with
    | (_typ,uu____4359)::(a1,uu____4361)::(a2,uu____4363)::[] ->
        let uu____4382 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4382 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___170_4386 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___170_4386.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___170_4386.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___171_4391 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___171_4391.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___171_4391.FStar_Syntax_Syntax.vars)
                })
         | uu____4394 -> FStar_Pervasives_Native.None)
    | (_typ,uu____4396)::uu____4397::(a1,uu____4399)::(a2,uu____4401)::[] ->
        let uu____4426 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4426 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___170_4430 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___170_4430.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___170_4430.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___171_4435 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___171_4435.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___171_4435.FStar_Syntax_Syntax.vars)
                })
         | uu____4438 -> FStar_Pervasives_Native.None)
    | uu____4439 -> failwith "Unexpected number of arguments" in
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
      let uu____4451 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops cfg.steps) in
      if uu____4451
      then tm
      else
        (let uu____4453 = FStar_Syntax_Util.head_and_args tm in
         match uu____4453 with
         | (head1,args) ->
             let uu____4473 =
               let uu____4474 = FStar_Syntax_Util.un_uinst head1 in
               uu____4474.FStar_Syntax_Syntax.n in
             (match uu____4473 with
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____4477 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps in
                  (match uu____4477 with
                   | FStar_Pervasives_Native.None  -> tm
                   | FStar_Pervasives_Native.Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then tm
                       else
                         (let uu____4492 =
                            prim_step.interpretation
                              head1.FStar_Syntax_Syntax.pos args in
                          match uu____4492 with
                          | FStar_Pervasives_Native.None  -> tm
                          | FStar_Pervasives_Native.Some reduced -> reduced))
              | uu____4495 -> tm))
let reduce_equality:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___172_4506 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___172_4506.tcenv);
           delta_level = (uu___172_4506.delta_level);
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
        let uu___173_4525 = t in
        {
          FStar_Syntax_Syntax.n = (uu___173_4525.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___173_4525.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid ->
            FStar_Pervasives_Native.Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid ->
            FStar_Pervasives_Native.Some false
        | uu____4539 -> FStar_Pervasives_Native.None in
      let simplify arg = ((simp_t (FStar_Pervasives_Native.fst arg)), arg) in
      let tm1 = reduce_primops cfg tm in
      let uu____4562 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps) in
      if uu____4562
      then tm1
      else
        (match tm1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.pos = uu____4565;
                     FStar_Syntax_Syntax.vars = uu____4566;_},uu____4567);
                FStar_Syntax_Syntax.pos = uu____4568;
                FStar_Syntax_Syntax.vars = uu____4569;_},args)
             ->
             let uu____4583 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
             if uu____4583
             then
               let uu____4584 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____4584 with
                | (FStar_Pervasives_Native.Some (true ),uu____4612)::
                    (uu____4613,(arg,uu____4615))::[] -> arg
                | (uu____4648,(arg,uu____4650))::(FStar_Pervasives_Native.Some
                                                  (true ),uu____4651)::[]
                    -> arg
                | (FStar_Pervasives_Native.Some (false ),uu____4684)::uu____4685::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____4717::(FStar_Pervasives_Native.Some (false
                               ),uu____4718)::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____4750 -> tm1)
             else
               (let uu____4759 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
                if uu____4759
                then
                  let uu____4760 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____4760 with
                  | (FStar_Pervasives_Native.Some (true ),uu____4788)::uu____4789::[]
                      -> w FStar_Syntax_Util.t_true
                  | uu____4821::(FStar_Pervasives_Native.Some (true
                                 ),uu____4822)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____4854)::
                      (uu____4855,(arg,uu____4857))::[] -> arg
                  | (uu____4890,(arg,uu____4892))::(FStar_Pervasives_Native.Some
                                                    (false ),uu____4893)::[]
                      -> arg
                  | uu____4926 -> tm1
                else
                  (let uu____4935 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.imp_lid in
                   if uu____4935
                   then
                     let uu____4936 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____4936 with
                     | uu____4964::(FStar_Pervasives_Native.Some (true
                                    ),uu____4965)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____4997)::uu____4998::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____5030)::
                         (uu____5031,(arg,uu____5033))::[] -> arg
                     | (uu____5066,(p,uu____5068))::(uu____5069,(q,uu____5071))::[]
                         ->
                         let uu____5104 = FStar_Syntax_Util.term_eq p q in
                         (if uu____5104
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____5106 -> tm1
                   else
                     (let uu____5115 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____5115
                      then
                        let uu____5116 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____5116 with
                        | (FStar_Pervasives_Native.Some (true ),uu____5144)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____5164)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____5184 -> tm1
                      else
                        (let uu____5193 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____5193
                         then
                           match args with
                           | (t,uu____5195)::[] ->
                               let uu____5204 =
                                 let uu____5205 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5205.FStar_Syntax_Syntax.n in
                               (match uu____5204 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5207::[],body,uu____5209) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____5223 -> tm1)
                                | uu____5225 -> tm1)
                           | (uu____5226,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____5227))::
                               (t,uu____5229)::[] ->
                               let uu____5249 =
                                 let uu____5250 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5250.FStar_Syntax_Syntax.n in
                               (match uu____5249 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5252::[],body,uu____5254) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____5268 -> tm1)
                                | uu____5270 -> tm1)
                           | uu____5271 -> tm1
                         else
                           (let uu____5277 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____5277
                            then
                              match args with
                              | (t,uu____5279)::[] ->
                                  let uu____5288 =
                                    let uu____5289 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5289.FStar_Syntax_Syntax.n in
                                  (match uu____5288 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5291::[],body,uu____5293) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____5307 -> tm1)
                                   | uu____5309 -> tm1)
                              | (uu____5310,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____5311))::
                                  (t,uu____5313)::[] ->
                                  let uu____5333 =
                                    let uu____5334 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5334.FStar_Syntax_Syntax.n in
                                  (match uu____5333 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5336::[],body,uu____5338) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____5352 -> tm1)
                                   | uu____5354 -> tm1)
                              | uu____5355 -> tm1
                            else reduce_equality cfg tm1)))))
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                FStar_Syntax_Syntax.pos = uu____5362;
                FStar_Syntax_Syntax.vars = uu____5363;_},args)
             ->
             let uu____5375 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
             if uu____5375
             then
               let uu____5376 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____5376 with
                | (FStar_Pervasives_Native.Some (true ),uu____5404)::
                    (uu____5405,(arg,uu____5407))::[] -> arg
                | (uu____5440,(arg,uu____5442))::(FStar_Pervasives_Native.Some
                                                  (true ),uu____5443)::[]
                    -> arg
                | (FStar_Pervasives_Native.Some (false ),uu____5476)::uu____5477::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____5509::(FStar_Pervasives_Native.Some (false
                               ),uu____5510)::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____5542 -> tm1)
             else
               (let uu____5551 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
                if uu____5551
                then
                  let uu____5552 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____5552 with
                  | (FStar_Pervasives_Native.Some (true ),uu____5580)::uu____5581::[]
                      -> w FStar_Syntax_Util.t_true
                  | uu____5613::(FStar_Pervasives_Native.Some (true
                                 ),uu____5614)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____5646)::
                      (uu____5647,(arg,uu____5649))::[] -> arg
                  | (uu____5682,(arg,uu____5684))::(FStar_Pervasives_Native.Some
                                                    (false ),uu____5685)::[]
                      -> arg
                  | uu____5718 -> tm1
                else
                  (let uu____5727 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.imp_lid in
                   if uu____5727
                   then
                     let uu____5728 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____5728 with
                     | uu____5756::(FStar_Pervasives_Native.Some (true
                                    ),uu____5757)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____5789)::uu____5790::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____5822)::
                         (uu____5823,(arg,uu____5825))::[] -> arg
                     | (uu____5858,(p,uu____5860))::(uu____5861,(q,uu____5863))::[]
                         ->
                         let uu____5896 = FStar_Syntax_Util.term_eq p q in
                         (if uu____5896
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____5898 -> tm1
                   else
                     (let uu____5907 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____5907
                      then
                        let uu____5908 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____5908 with
                        | (FStar_Pervasives_Native.Some (true ),uu____5936)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____5956)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____5976 -> tm1
                      else
                        (let uu____5985 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____5985
                         then
                           match args with
                           | (t,uu____5987)::[] ->
                               let uu____5996 =
                                 let uu____5997 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5997.FStar_Syntax_Syntax.n in
                               (match uu____5996 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5999::[],body,uu____6001) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____6015 -> tm1)
                                | uu____6017 -> tm1)
                           | (uu____6018,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____6019))::
                               (t,uu____6021)::[] ->
                               let uu____6041 =
                                 let uu____6042 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____6042.FStar_Syntax_Syntax.n in
                               (match uu____6041 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____6044::[],body,uu____6046) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____6060 -> tm1)
                                | uu____6062 -> tm1)
                           | uu____6063 -> tm1
                         else
                           (let uu____6069 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____6069
                            then
                              match args with
                              | (t,uu____6071)::[] ->
                                  let uu____6080 =
                                    let uu____6081 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____6081.FStar_Syntax_Syntax.n in
                                  (match uu____6080 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6083::[],body,uu____6085) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____6099 -> tm1)
                                   | uu____6101 -> tm1)
                              | (uu____6102,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____6103))::
                                  (t,uu____6105)::[] ->
                                  let uu____6125 =
                                    let uu____6126 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____6126.FStar_Syntax_Syntax.n in
                                  (match uu____6125 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6128::[],body,uu____6130) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____6144 -> tm1)
                                   | uu____6146 -> tm1)
                              | uu____6147 -> tm1
                            else reduce_equality cfg tm1)))))
         | uu____6153 -> tm1)
let is_norm_request hd1 args =
  let uu____6171 =
    let uu____6175 =
      let uu____6176 = FStar_Syntax_Util.un_uinst hd1 in
      uu____6176.FStar_Syntax_Syntax.n in
    (uu____6175, args) in
  match uu____6171 with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6180::uu____6181::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6184::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
  | uu____6186 -> false
let get_norm_request args =
  match args with
  | uu____6208::(tm,uu____6210)::[] -> tm
  | (tm,uu____6220)::[] -> tm
  | uu____6225 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___144_6233  ->
    match uu___144_6233 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.pos = uu____6235;
           FStar_Syntax_Syntax.vars = uu____6236;_},uu____6237,uu____6238))::uu____6239
        -> true
    | uu____6243 -> false
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
            (fun uu____6357  ->
               let uu____6358 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____6359 = FStar_Syntax_Print.term_to_string t1 in
               let uu____6360 =
                 let uu____6361 =
                   let uu____6363 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6363 in
                 stack_to_string uu____6361 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____6358
                 uu____6359 uu____6360);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____6375 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____6388 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____6397 =
                 let uu____6398 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____6399 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____6398 uu____6399 in
               failwith uu____6397
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____6400 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____6409 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____6410 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6411;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____6412;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6414;
                 FStar_Syntax_Syntax.fv_delta = uu____6415;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6416;
                 FStar_Syntax_Syntax.fv_delta = uu____6417;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____6418);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (FStar_Syntax_Util.is_fstar_tactics_embed hd1) ||
                 (FStar_Syntax_Util.is_fstar_tactics_by_tactic hd1)
               ->
               let args1 = closures_as_args_delayed cfg env args in
               let hd2 = closure_as_term cfg env hd1 in
               let t2 =
                 let uu___174_6442 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___174_6442.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___174_6442.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____6463 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____6463) && (is_norm_request hd1 args))
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
                 let uu___175_6473 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___175_6473.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___175_6473.primitive_steps)
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
                  FStar_Syntax_Syntax.pos = uu____6478;
                  FStar_Syntax_Syntax.vars = uu____6479;_},a1::a2::rest)
               ->
               let uu____6505 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6505 with
                | (hd1,uu____6514) ->
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
                    (FStar_Const.Const_reflect uu____6554);
                  FStar_Syntax_Syntax.pos = uu____6555;
                  FStar_Syntax_Syntax.vars = uu____6556;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____6573 = FStar_List.tl stack1 in
               norm cfg env uu____6573 (FStar_Pervasives_Native.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____6575;
                  FStar_Syntax_Syntax.vars = uu____6576;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____6593 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6593 with
                | (reify_head,uu____6602) ->
                    let a1 =
                      let uu____6614 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (FStar_Pervasives_Native.fst a) in
                      FStar_Syntax_Subst.compress uu____6614 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____6616);
                            FStar_Syntax_Syntax.pos = uu____6617;
                            FStar_Syntax_Syntax.vars = uu____6618;_},a2::[])
                         ->
                         norm cfg env stack1 (FStar_Pervasives_Native.fst a2)
                     | uu____6636 ->
                         let stack2 =
                           (App
                              (reify_head, FStar_Pervasives_Native.None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____6643 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____6643
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____6648 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____6648
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____6651 =
                      let uu____6655 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____6655, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____6651 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___145_6665  ->
                         match uu___145_6665 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____6668 =
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
                 if uu____6668 then false else should_delta in
               if Prims.op_Negation should_delta1
               then rebuild cfg env stack1 t1
               else
                 (let r_env =
                    let uu____6672 = FStar_Syntax_Syntax.range_of_fv f in
                    FStar_TypeChecker_Env.set_range cfg.tcenv uu____6672 in
                  let uu____6673 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  match uu____6673 with
                  | FStar_Pervasives_Native.None  ->
                      (log cfg
                         (fun uu____6681  ->
                            FStar_Util.print "Tm_fvar case 2\n" []);
                       rebuild cfg env stack1 t1)
                  | FStar_Pervasives_Native.Some (us,t2) ->
                      (log cfg
                         (fun uu____6690  ->
                            let uu____6691 =
                              FStar_Syntax_Print.term_to_string t0 in
                            let uu____6692 =
                              FStar_Syntax_Print.term_to_string t2 in
                            FStar_Util.print2 ">>> Unfolded %s to %s\n"
                              uu____6691 uu____6692);
                       (let t3 =
                          let uu____6694 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 (UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant)) in
                          if uu____6694
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
                          | (UnivArgs (us',uu____6706))::stack2 ->
                              let env1 =
                                FStar_All.pipe_right us'
                                  (FStar_List.fold_left
                                     (fun env1  -> fun u  -> (Univ u) :: env1)
                                     env) in
                              norm cfg env1 stack2 t3
                          | uu____6721 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack1 t3
                          | uu____6722 ->
                              let uu____6723 =
                                let uu____6724 =
                                  FStar_Syntax_Print.lid_to_string
                                    (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                FStar_Util.format1
                                  "Impossible: missing universe instantiation on %s"
                                  uu____6724 in
                              failwith uu____6723
                        else norm cfg env stack1 t3)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____6727 = lookup_bvar env x in
               (match uu____6727 with
                | Univ uu____6728 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____6743 = FStar_ST.read r in
                      (match uu____6743 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____6765  ->
                                 let uu____6766 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____6767 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____6766
                                   uu____6767);
                            (let uu____6768 =
                               let uu____6769 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____6769.FStar_Syntax_Syntax.n in
                             match uu____6768 with
                             | FStar_Syntax_Syntax.Tm_abs uu____6771 ->
                                 norm cfg env2 stack1 t'
                             | uu____6780 -> rebuild cfg env2 stack1 t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____6801)::uu____6802 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____6807)::uu____6808 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____6814,uu____6815))::stack_rest ->
                    (match c with
                     | Univ uu____6818 -> norm cfg (c :: env) stack_rest t1
                     | uu____6819 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____6822::[] ->
                              (match lopt with
                               | FStar_Pervasives_Native.None  when
                                   FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____6832  ->
                                         let uu____6833 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6833);
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
                                           (fun uu___146_6837  ->
                                              match uu___146_6837 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____6838 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____6842  ->
                                         let uu____6843 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6843);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____6844 when
                                   (FStar_All.pipe_right cfg.steps
                                      (FStar_List.contains Reify))
                                     ||
                                     (FStar_All.pipe_right cfg.steps
                                        (FStar_List.contains CheckNoUvars))
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____6846 ->
                                   let cfg1 =
                                     let uu___176_6849 = cfg in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___176_6849.tcenv);
                                       delta_level =
                                         (uu___176_6849.delta_level);
                                       primitive_steps =
                                         (uu___176_6849.primitive_steps)
                                     } in
                                   let uu____6850 =
                                     closure_as_term cfg1 env t1 in
                                   rebuild cfg1 env stack1 uu____6850)
                          | uu____6851::tl1 ->
                              (log cfg
                                 (fun uu____6863  ->
                                    let uu____6864 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____6864);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___177_6883 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___177_6883.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____6898  ->
                          let uu____6899 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____6899);
                     norm cfg env stack2 t1)
                | (Debug uu____6900)::uu____6901 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____6903 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____6903
                    else
                      (let uu____6905 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____6905 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____6921  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____6931 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____6931
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____6938 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____6938)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___178_6942 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___178_6942.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___178_6942.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____6943 -> lopt in
                           (log cfg
                              (fun uu____6948  ->
                                 let uu____6949 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____6949);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___179_6961 = cfg in
                               let uu____6962 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___179_6961.steps);
                                 tcenv = (uu___179_6961.tcenv);
                                 delta_level = (uu___179_6961.delta_level);
                                 primitive_steps = uu____6962
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____6968)::uu____6969 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____6973 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____6973
                    else
                      (let uu____6975 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____6975 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____6991  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____7001 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____7001
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____7008 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____7008)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___178_7012 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___178_7012.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___178_7012.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____7013 -> lopt in
                           (log cfg
                              (fun uu____7018  ->
                                 let uu____7019 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7019);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___179_7031 = cfg in
                               let uu____7032 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___179_7031.steps);
                                 tcenv = (uu___179_7031.tcenv);
                                 delta_level = (uu___179_7031.delta_level);
                                 primitive_steps = uu____7032
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____7038)::uu____7039 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7045 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7045
                    else
                      (let uu____7047 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7047 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7063  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____7073 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____7073
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____7080 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____7080)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___178_7084 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___178_7084.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___178_7084.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____7085 -> lopt in
                           (log cfg
                              (fun uu____7090  ->
                                 let uu____7091 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7091);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___179_7103 = cfg in
                               let uu____7104 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___179_7103.steps);
                                 tcenv = (uu___179_7103.tcenv);
                                 delta_level = (uu___179_7103.delta_level);
                                 primitive_steps = uu____7104
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____7110)::uu____7111 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7116 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7116
                    else
                      (let uu____7118 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7118 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7134  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____7144 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____7144
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____7151 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____7151)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___178_7155 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___178_7155.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___178_7155.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____7156 -> lopt in
                           (log cfg
                              (fun uu____7161  ->
                                 let uu____7162 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7162);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___179_7174 = cfg in
                               let uu____7175 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___179_7174.steps);
                                 tcenv = (uu___179_7174.tcenv);
                                 delta_level = (uu___179_7174.delta_level);
                                 primitive_steps = uu____7175
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____7181)::uu____7182 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7190 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7190
                    else
                      (let uu____7192 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7192 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7208  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____7218 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____7218
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____7225 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____7225)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___178_7229 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___178_7229.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___178_7229.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____7230 -> lopt in
                           (log cfg
                              (fun uu____7235  ->
                                 let uu____7236 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7236);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___179_7248 = cfg in
                               let uu____7249 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___179_7248.steps);
                                 tcenv = (uu___179_7248.tcenv);
                                 delta_level = (uu___179_7248.delta_level);
                                 primitive_steps = uu____7249
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7255 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7255
                    else
                      (let uu____7257 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7257 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7273  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____7283 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____7283
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____7290 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____7290)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___178_7294 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___178_7294.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___178_7294.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____7295 -> lopt in
                           (log cfg
                              (fun uu____7300  ->
                                 let uu____7301 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7301);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___179_7313 = cfg in
                               let uu____7314 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___179_7313.steps);
                                 tcenv = (uu___179_7313.tcenv);
                                 delta_level = (uu___179_7313.delta_level);
                                 primitive_steps = uu____7314
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
                      (fun uu____7343  ->
                         fun stack2  ->
                           match uu____7343 with
                           | (a,aq) ->
                               let uu____7351 =
                                 let uu____7352 =
                                   let uu____7356 =
                                     let uu____7357 =
                                       let uu____7367 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____7367, false) in
                                     Clos uu____7357 in
                                   (uu____7356, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____7352 in
                               uu____7351 :: stack2) args) in
               (log cfg
                  (fun uu____7391  ->
                     let uu____7392 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____7392);
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
                             ((let uu___180_7411 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___180_7411.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___180_7411.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____7412 ->
                      let uu____7415 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7415)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____7418 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____7418 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____7433 =
                          let uu____7434 =
                            let uu____7438 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___181_7440 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___181_7440.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___181_7440.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____7438) in
                          FStar_Syntax_Syntax.Tm_refine uu____7434 in
                        mk uu____7433 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____7451 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____7451
               else
                 (let uu____7453 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____7453 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____7459 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  -> fun uu____7467  -> Dummy :: env1)
                               env) in
                        norm_comp cfg uu____7459 c1 in
                      let t2 =
                        let uu____7473 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____7473 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____7505)::uu____7506 -> norm cfg env stack1 t11
                | (Arg uu____7511)::uu____7512 -> norm cfg env stack1 t11
                | (App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____7517;
                       FStar_Syntax_Syntax.vars = uu____7518;_},uu____7519,uu____7520))::uu____7521
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____7525)::uu____7526 ->
                    norm cfg env stack1 t11
                | uu____7531 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____7535  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____7545 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____7545
                        | FStar_Util.Inr c ->
                            let uu____7550 = norm_comp cfg env c in
                            FStar_Util.Inr uu____7550 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____7554 =
                        let uu____7555 =
                          let uu____7556 =
                            let uu____7570 = FStar_Syntax_Util.unascribe t12 in
                            (uu____7570, (tc1, tacopt1), l) in
                          FStar_Syntax_Syntax.Tm_ascribed uu____7556 in
                        mk uu____7555 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____7554)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____7610,{
                              FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                uu____7611;
                              FStar_Syntax_Syntax.lbunivs = uu____7612;
                              FStar_Syntax_Syntax.lbtyp = uu____7613;
                              FStar_Syntax_Syntax.lbeff = uu____7614;
                              FStar_Syntax_Syntax.lbdef = uu____7615;_}::uu____7616),uu____7617)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____7637 =
                 (let uu____7640 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____7640) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____7642 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____7642))) in
               if uu____7637
               then
                 let env1 =
                   let uu____7645 =
                     let uu____7646 =
                       let uu____7656 =
                         FStar_Util.mk_ref FStar_Pervasives_Native.None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____7656,
                         false) in
                     Clos uu____7646 in
                   uu____7645 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____7679 =
                    let uu____7682 =
                      let uu____7683 =
                        let uu____7684 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____7684
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____7683] in
                    FStar_Syntax_Subst.open_term uu____7682 body in
                  match uu____7679 with
                  | (bs,body1) ->
                      let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                      let lbname =
                        let x =
                          let uu____7694 = FStar_List.hd bs in
                          FStar_Pervasives_Native.fst uu____7694 in
                        FStar_Util.Inl
                          (let uu___182_7700 = x in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___182_7700.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___182_7700.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = ty
                           }) in
                      let lb1 =
                        let uu___183_7702 = lb in
                        let uu____7703 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = lbname;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___183_7702.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = ty;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___183_7702.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____7703
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____7714  -> Dummy :: env1)
                             env) in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let ((true ,lbs),body) when
               FStar_List.contains CompressUvars cfg.steps ->
               let uu____7727 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____7727 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____7755 =
                               let uu___184_7756 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___184_7756.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___184_7756.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____7755 in
                           let uu____7757 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____7757 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____7770 =
                                   FStar_List.map (fun uu____7773  -> Dummy)
                                     lbs1 in
                                 let uu____7774 =
                                   let uu____7776 =
                                     FStar_List.map
                                       (fun uu____7781  -> Dummy) xs1 in
                                   FStar_List.append uu____7776 env in
                                 FStar_List.append uu____7770 uu____7774 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____7789 =
                                       let uu___185_7790 = rc in
                                       let uu____7791 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___185_7790.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____7791;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___185_7790.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____7789
                                 | uu____7795 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___186_7798 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___186_7798.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___186_7798.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____7801 =
                        FStar_List.map (fun uu____7804  -> Dummy) lbs2 in
                      FStar_List.append uu____7801 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____7806 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____7806 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___187_7816 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___187_7816.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___187_7816.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____7833 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____7833
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____7844 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____7875  ->
                        match uu____7875 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____7914 =
                                let uu___188_7915 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___188_7915.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___188_7915.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____7914 in
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
               (match uu____7844 with
                | (rec_env,memos,uu____7973) ->
                    let uu____7988 =
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
                             let uu____8030 =
                               let uu____8031 =
                                 let uu____8041 =
                                   FStar_Util.mk_ref
                                     FStar_Pervasives_Native.None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____8041, false) in
                               Clos uu____8031 in
                             uu____8030 :: env1)
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
                             FStar_Syntax_Syntax.pos = uu____8074;
                             FStar_Syntax_Syntax.vars = uu____8075;_},uu____8076,uu____8077))::uu____8078
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____8082 -> false in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____8089 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____8089
                        then
                          let uu___189_8090 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___189_8090.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps = (uu___189_8090.primitive_steps)
                          }
                        else
                          (let uu___190_8092 = cfg in
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___190_8092.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta];
                             primitive_steps =
                               (uu___190_8092.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____8094 =
                         let uu____8095 = FStar_Syntax_Subst.compress head1 in
                         uu____8095.FStar_Syntax_Syntax.n in
                       match uu____8094 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____8106 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8106 with
                            | (uu____8107,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____8111 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____8118 =
                                         let uu____8119 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____8119.FStar_Syntax_Syntax.n in
                                       match uu____8118 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____8123,uu____8124))
                                           ->
                                           let uu____8129 =
                                             let uu____8130 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____8130.FStar_Syntax_Syntax.n in
                                           (match uu____8129 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____8134,msrc,uu____8136))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____8141 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____8141
                                            | uu____8142 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____8143 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____8144 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____8144 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___191_8148 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___191_8148.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___191_8148.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___191_8148.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____8149 =
                                            FStar_List.tl stack1 in
                                          let uu____8150 =
                                            let uu____8151 =
                                              let uu____8153 =
                                                let uu____8154 =
                                                  let uu____8161 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____8161) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____8154 in
                                              FStar_Syntax_Syntax.mk
                                                uu____8153 in
                                            uu____8151
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____8149 uu____8150
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____8174 =
                                            let uu____8175 = is_return body in
                                            match uu____8175 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____8178;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____8179;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____8182 -> false in
                                          if uu____8174
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
                                               let uu____8197 =
                                                 let uu____8199 =
                                                   let uu____8200 =
                                                     let uu____8209 =
                                                       let uu____8211 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____8211] in
                                                     (uu____8209, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc)) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____8200 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8199 in
                                               uu____8197
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____8226 =
                                                 let uu____8227 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____8227.FStar_Syntax_Syntax.n in
                                               match uu____8226 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____8231::uu____8232::[])
                                                   ->
                                                   let uu____8236 =
                                                     let uu____8238 =
                                                       let uu____8239 =
                                                         let uu____8243 =
                                                           let uu____8245 =
                                                             let uu____8246 =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____8246 in
                                                           let uu____8247 =
                                                             let uu____8249 =
                                                               let uu____8250
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____8250 in
                                                             [uu____8249] in
                                                           uu____8245 ::
                                                             uu____8247 in
                                                         (bind1, uu____8243) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____8239 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8238 in
                                                   uu____8236
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____8259 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____8263 =
                                                 let uu____8265 =
                                                   let uu____8266 =
                                                     let uu____8274 =
                                                       let uu____8276 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____8277 =
                                                         let uu____8279 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____8280 =
                                                           let uu____8282 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____8283 =
                                                             let uu____8285 =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____8286 =
                                                               let uu____8288
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____8289
                                                                 =
                                                                 let uu____8291
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____8291] in
                                                               uu____8288 ::
                                                                 uu____8289 in
                                                             uu____8285 ::
                                                               uu____8286 in
                                                           uu____8282 ::
                                                             uu____8283 in
                                                         uu____8279 ::
                                                           uu____8280 in
                                                       uu____8276 ::
                                                         uu____8277 in
                                                     (bind_inst, uu____8274) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____8266 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8265 in
                                               uu____8263
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____8300 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____8300 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____8314 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8314 with
                            | (uu____8315,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____8335 =
                                        let uu____8336 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____8336.FStar_Syntax_Syntax.n in
                                      match uu____8335 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____8340) -> t4
                                      | uu____8343 -> head2 in
                                    let uu____8344 =
                                      let uu____8345 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____8345.FStar_Syntax_Syntax.n in
                                    match uu____8344 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____8349 ->
                                        FStar_Pervasives_Native.None in
                                  let uu____8350 = maybe_extract_fv head2 in
                                  match uu____8350 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____8356 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____8356
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____8360 =
                                          maybe_extract_fv head3 in
                                        match uu____8360 with
                                        | FStar_Pervasives_Native.Some
                                            uu____8363 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____8364 ->
                                            FStar_Pervasives_Native.Some
                                              false in
                                      (head3, action_unfolded)
                                  | uu____8367 ->
                                      (head2, FStar_Pervasives_Native.None) in
                                ((let is_arg_impure uu____8377 =
                                    match uu____8377 with
                                    | (e,q) ->
                                        let uu____8382 =
                                          let uu____8383 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____8383.FStar_Syntax_Syntax.n in
                                        (match uu____8382 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____8393 -> false) in
                                  let uu____8394 =
                                    let uu____8395 =
                                      let uu____8399 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____8399 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____8395 in
                                  if uu____8394
                                  then
                                    let uu____8402 =
                                      let uu____8403 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____8403 in
                                    failwith uu____8402
                                  else ());
                                 (let uu____8405 =
                                    maybe_unfold_action head_app in
                                  match uu____8405 with
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
                                      let uu____8432 = FStar_List.tl stack1 in
                                      norm cfg env uu____8432 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____8442 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____8442 in
                           let uu____8443 = FStar_List.tl stack1 in
                           norm cfg env uu____8443 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____8508  ->
                                     match uu____8508 with
                                     | (pat,wopt,tm) ->
                                         let uu____8534 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____8534))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____8551 = FStar_List.tl stack1 in
                           norm cfg env uu____8551 tm
                       | uu____8552 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.pos = uu____8559;
                             FStar_Syntax_Syntax.vars = uu____8560;_},uu____8561,uu____8562))::uu____8563
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____8567 -> false in
                    if should_reify
                    then
                      let uu____8568 = FStar_List.tl stack1 in
                      let uu____8569 =
                        let uu____8570 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____8570 in
                      norm cfg env uu____8568 uu____8569
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____8573 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____8573
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___192_8579 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___192_8579.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___192_8579.primitive_steps)
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
                | uu____8581 ->
                    (match stack1 with
                     | uu____8582::uu____8583 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____8587)
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
                          | uu____8602 -> norm cfg env stack1 head1)
                     | [] ->
                         let head2 = norm cfg env [] head1 in
                         let m1 =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               let uu____8611 =
                                 norm_pattern_args cfg env args in
                               FStar_Syntax_Syntax.Meta_pattern uu____8611
                           | uu____8617 -> m in
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
              let uu____8627 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____8627 with
              | (uu____8628,return_repr) ->
                  let return_inst =
                    let uu____8634 =
                      let uu____8635 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____8635.FStar_Syntax_Syntax.n in
                    match uu____8634 with
                    | FStar_Syntax_Syntax.Tm_uinst (return_tm,uu____8639::[])
                        ->
                        let uu____8643 =
                          let uu____8645 =
                            let uu____8646 =
                              let uu____8650 =
                                let uu____8652 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____8652] in
                              (return_tm, uu____8650) in
                            FStar_Syntax_Syntax.Tm_uinst uu____8646 in
                          FStar_Syntax_Syntax.mk uu____8645 in
                        uu____8643 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____8661 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____8663 =
                    let uu____8665 =
                      let uu____8666 =
                        let uu____8674 =
                          let uu____8676 = FStar_Syntax_Syntax.as_arg t in
                          let uu____8677 =
                            let uu____8679 = FStar_Syntax_Syntax.as_arg e in
                            [uu____8679] in
                          uu____8676 :: uu____8677 in
                        (return_inst, uu____8674) in
                      FStar_Syntax_Syntax.Tm_app uu____8666 in
                    FStar_Syntax_Syntax.mk uu____8665 in
                  uu____8663 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____8689 = FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____8689 with
               | FStar_Pervasives_Native.None  ->
                   let uu____8691 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____8691
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____8692;
                     FStar_TypeChecker_Env.mtarget = uu____8693;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____8694;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____8705;
                     FStar_TypeChecker_Env.mtarget = uu____8706;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____8707;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____8725 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____8725)
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
                (fun uu____8757  ->
                   match uu____8757 with
                   | (a,imp) ->
                       let uu____8764 = norm cfg env [] a in
                       (uu____8764, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___193_8776 = comp1 in
            let uu____8778 =
              let uu____8779 =
                let uu____8784 = norm cfg env [] t in
                let uu____8785 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____8784, uu____8785) in
              FStar_Syntax_Syntax.Total uu____8779 in
            {
              FStar_Syntax_Syntax.n = uu____8778;
              FStar_Syntax_Syntax.pos =
                (uu___193_8776.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___193_8776.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___194_8796 = comp1 in
            let uu____8798 =
              let uu____8799 =
                let uu____8804 = norm cfg env [] t in
                let uu____8805 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____8804, uu____8805) in
              FStar_Syntax_Syntax.GTotal uu____8799 in
            {
              FStar_Syntax_Syntax.n = uu____8798;
              FStar_Syntax_Syntax.pos =
                (uu___194_8796.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___194_8796.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____8838  ->
                      match uu____8838 with
                      | (a,i) ->
                          let uu____8845 = norm cfg env [] a in
                          (uu____8845, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___147_8853  ->
                      match uu___147_8853 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____8856 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____8856
                      | f -> f)) in
            let uu___195_8859 = comp1 in
            let uu____8861 =
              let uu____8862 =
                let uu___196_8863 = ct in
                let uu____8864 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____8865 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____8867 = norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____8864;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___196_8863.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____8865;
                  FStar_Syntax_Syntax.effect_args = uu____8867;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____8862 in
            {
              FStar_Syntax_Syntax.n = uu____8861;
              FStar_Syntax_Syntax.pos =
                (uu___195_8859.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___195_8859.FStar_Syntax_Syntax.vars)
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
            (let uu___197_8883 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___197_8883.tcenv);
               delta_level = (uu___197_8883.delta_level);
               primitive_steps = (uu___197_8883.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____8888 = norm1 t in
          FStar_Syntax_Util.non_informative uu____8888 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____8890 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___198_8901 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.pos =
                (uu___198_8901.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___198_8901.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____8908 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____8908
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
                    let uu___199_8916 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___199_8916.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___199_8916.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___199_8916.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___200_8918 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___200_8918.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___200_8918.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___200_8918.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___200_8918.FStar_Syntax_Syntax.flags)
                    } in
              let uu___201_8919 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos =
                  (uu___201_8919.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___201_8919.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____8923 -> c
and norm_binder:
  cfg ->
    env ->
      FStar_Syntax_Syntax.binder ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
          FStar_Pervasives_Native.tuple2
  =
  fun cfg  ->
    fun env  ->
      fun uu____8926  ->
        match uu____8926 with
        | (x,imp) ->
            let uu____8929 =
              let uu___202_8930 = x in
              let uu____8931 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___202_8930.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___202_8930.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____8931
              } in
            (uu____8929, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____8936 =
          FStar_List.fold_left
            (fun uu____8948  ->
               fun b  ->
                 match uu____8948 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____8936 with | (nbs,uu____8965) -> FStar_List.rev nbs
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
            let uu____8976 =
              let uu___203_8977 = rc in
              let uu____8978 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___203_8977.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____8978;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___203_8977.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____8976
        | uu____8982 -> lopt
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
              ((let uu____8992 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____8992
                then
                  let uu____8993 = FStar_Syntax_Print.term_to_string tm in
                  let uu____8994 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2 "Normalized %s to %s\n" uu____8993
                    uu____8994
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___204_9007 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___204_9007.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____9028  ->
                    let uu____9029 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____9029);
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
              let uu____9058 =
                let uu___205_9059 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___205_9059.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___205_9059.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____9058
          | (Arg (Univ uu____9062,uu____9063,uu____9064))::uu____9065 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____9067,uu____9068))::uu____9069 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____9081),aq,r))::stack2 ->
              (log cfg
                 (fun uu____9099  ->
                    let uu____9100 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____9100);
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
                 (let uu____9110 = FStar_ST.read m in
                  match uu____9110 with
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
                  | FStar_Pervasives_Native.Some (uu____9135,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq)
                          FStar_Pervasives_Native.None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 =
                FStar_Syntax_Syntax.extend_app head1 (t, aq)
                  FStar_Pervasives_Native.None r in
              let uu____9155 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____9155
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____9164  ->
                    let uu____9165 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____9165);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____9170 =
                  log cfg
                    (fun uu____9175  ->
                       let uu____9176 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____9177 =
                         let uu____9178 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____9189  ->
                                   match uu____9189 with
                                   | (p,uu____9195,uu____9196) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____9178
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____9176 uu____9177);
                  (let whnf = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___148_9207  ->
                               match uu___148_9207 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____9208 -> false)) in
                     let steps' =
                       let uu____9211 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____9211
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___206_9214 = cfg in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___206_9214.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___206_9214.primitive_steps)
                     } in
                   let norm_or_whnf env2 t1 =
                     if whnf
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____9244 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____9257 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____9295  ->
                                   fun uu____9296  ->
                                     match (uu____9295, uu____9296) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____9350 = norm_pat env3 p1 in
                                         (match uu____9350 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____9257 with
                          | (pats1,env3) ->
                              ((let uu___207_9404 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.p =
                                    (uu___207_9404.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___208_9415 = x in
                           let uu____9416 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___208_9415.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___208_9415.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9416
                           } in
                         ((let uu___209_9421 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.p =
                               (uu___209_9421.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___210_9425 = x in
                           let uu____9426 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___210_9425.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___210_9425.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9426
                           } in
                         ((let uu___211_9431 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.p =
                               (uu___211_9431.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___212_9438 = x in
                           let uu____9439 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___212_9438.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___212_9438.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9439
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___213_9445 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.p =
                               (uu___213_9445.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf -> branches
                     | uu____9448 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____9461 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____9461 with
                                 | (p,wopt,e) ->
                                     let uu____9473 = norm_pat env1 p in
                                     (match uu____9473 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Pervasives_Native.Some w
                                                ->
                                                let uu____9491 =
                                                  norm_or_whnf env2 w in
                                                FStar_Pervasives_Native.Some
                                                  uu____9491 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____9495 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____9495) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____9503) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____9506 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____9507;
                        FStar_Syntax_Syntax.fv_delta = uu____9508;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Data_ctor );_}
                      -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____9509;
                        FStar_Syntax_Syntax.fv_delta = uu____9510;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Record_ctor uu____9511);_}
                      -> true
                  | uu____9515 -> false in
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
                  let uu____9594 = FStar_Syntax_Util.head_and_args scrutinee1 in
                  match uu____9594 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var uu____9620 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_wild uu____9622 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____9624 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee1.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____9635 ->
                                let uu____9636 =
                                  let uu____9637 = is_cons head1 in
                                  Prims.op_Negation uu____9637 in
                                FStar_Util.Inr uu____9636)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____9649 =
                             let uu____9650 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____9650.FStar_Syntax_Syntax.n in
                           (match uu____9649 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____9656 ->
                                let uu____9657 =
                                  let uu____9658 = is_cons head1 in
                                  Prims.op_Negation uu____9658 in
                                FStar_Util.Inr uu____9657))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____9687)::rest_a,(p1,uu____9690)::rest_p) ->
                      let uu____9713 = matches_pat t1 p1 in
                      (match uu____9713 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____9727 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____9784 = matches_pat scrutinee1 p1 in
                      (match uu____9784 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____9797  ->
                                 let uu____9798 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____9799 =
                                   let uu____9800 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____9800
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____9798 uu____9799);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____9812 =
                                        let uu____9813 =
                                          let uu____9823 =
                                            FStar_Util.mk_ref
                                              (FStar_Pervasives_Native.Some
                                                 ([], t1)) in
                                          ([], t1, uu____9823, false) in
                                        Clos uu____9813 in
                                      uu____9812 :: env2) env1 s in
                             let uu____9846 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____9846))) in
                let uu____9847 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____9847
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___149_9865  ->
                match uu___149_9865 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____9868 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____9872 -> d in
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
            let uu___214_9896 = config s e in
            {
              steps = (uu___214_9896.steps);
              tcenv = (uu___214_9896.tcenv);
              delta_level = (uu___214_9896.delta_level);
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
      fun t  -> let uu____9921 = config s e in norm_comp uu____9921 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  -> let uu____9930 = config [] env in norm_universe uu____9930 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun c  ->
      let uu____9939 = config [] env in ghost_to_pure_aux uu____9939 [] c
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
        let uu____9953 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____9953 in
      let uu____9954 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____9954
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___215_9956 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___215_9956.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___215_9956.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____9959  ->
                    let uu____9960 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____9960))
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
            ((let uu____9979 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____9979);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____9992 = config [AllowUnboundUniverses] env in
          norm_comp uu____9992 [] c
        with
        | e ->
            ((let uu____9999 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____9999);
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
                   let uu____10031 =
                     let uu____10032 =
                       let uu____10036 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____10036) in
                     FStar_Syntax_Syntax.Tm_refine uu____10032 in
                   mk uu____10031 t01.FStar_Syntax_Syntax.pos
               | uu____10039 -> t2)
          | uu____10040 -> t2 in
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
        let uu____10091 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____10091 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____10107 ->
                 let uu____10111 = FStar_Syntax_Util.abs_formals e in
                 (match uu____10111 with
                  | (actuals,uu____10117,uu____10118) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____10134 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____10134 with
                         | (binders,args) ->
                             let uu____10144 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____10144
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
      | uu____10156 ->
          let uu____10157 = FStar_Syntax_Util.head_and_args t in
          (match uu____10157 with
           | (head1,args) ->
               let uu____10177 =
                 let uu____10178 = FStar_Syntax_Subst.compress head1 in
                 uu____10178.FStar_Syntax_Syntax.n in
               (match uu____10177 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____10180,thead) ->
                    let uu____10194 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____10194 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____10225 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___220_10230 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___220_10230.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___220_10230.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___220_10230.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___220_10230.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___220_10230.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___220_10230.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___220_10230.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___220_10230.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___220_10230.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___220_10230.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___220_10230.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___220_10230.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___220_10230.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___220_10230.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___220_10230.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___220_10230.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___220_10230.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___220_10230.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___220_10230.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___220_10230.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___220_10230.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___220_10230.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___220_10230.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___220_10230.FStar_TypeChecker_Env.is_native_tactic)
                                 }) t in
                            match uu____10225 with
                            | (uu____10231,ty,uu____10233) ->
                                eta_expand_with_type env t ty))
                | uu____10234 ->
                    let uu____10235 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___221_10240 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___221_10240.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___221_10240.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___221_10240.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___221_10240.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___221_10240.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___221_10240.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___221_10240.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___221_10240.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___221_10240.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___221_10240.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___221_10240.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___221_10240.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___221_10240.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___221_10240.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___221_10240.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___221_10240.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___221_10240.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___221_10240.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___221_10240.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___221_10240.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___221_10240.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___221_10240.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___221_10240.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___221_10240.FStar_TypeChecker_Env.is_native_tactic)
                         }) t in
                    (match uu____10235 with
                     | (uu____10241,ty,uu____10243) ->
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
            | (uu____10292,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____10299,FStar_Util.Inl t) ->
                let uu____10303 =
                  let uu____10305 =
                    let uu____10306 =
                      let uu____10313 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____10313) in
                    FStar_Syntax_Syntax.Tm_arrow uu____10306 in
                  FStar_Syntax_Syntax.mk uu____10305 in
                uu____10303 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____10320 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____10320 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____10336 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____10364 ->
                    let uu____10365 =
                      let uu____10370 =
                        let uu____10371 = FStar_Syntax_Subst.compress t3 in
                        uu____10371.FStar_Syntax_Syntax.n in
                      (uu____10370, tc) in
                    (match uu____10365 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____10385) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____10405) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____10425,FStar_Util.Inl uu____10426) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____10438 -> failwith "Impossible") in
              (match uu____10336 with
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
          let uu____10502 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____10502 with
          | (univ_names1,binders1,tc) ->
              let uu____10533 = FStar_Util.left tc in
              (univ_names1, binders1, uu____10533)
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
          let uu____10561 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____10561 with
          | (univ_names1,binders1,tc) ->
              let uu____10593 = FStar_Util.right tc in
              (univ_names1, binders1, uu____10593)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____10618 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____10618 with
           | (univ_names1,binders1,typ1) ->
               let uu___222_10634 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___222_10634.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___222_10634.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___222_10634.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___222_10634.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___223_10646 = s in
          let uu____10647 =
            let uu____10648 =
              let uu____10653 = FStar_List.map (elim_uvars env) sigs in
              (uu____10653, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____10648 in
          {
            FStar_Syntax_Syntax.sigel = uu____10647;
            FStar_Syntax_Syntax.sigrng =
              (uu___223_10646.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___223_10646.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___223_10646.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___223_10646.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____10665 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____10665 with
           | (univ_names1,uu____10675,typ1) ->
               let uu___224_10683 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___224_10683.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___224_10683.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___224_10683.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___224_10683.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____10688 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____10688 with
           | (univ_names1,uu____10698,typ1) ->
               let uu___225_10706 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___225_10706.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___225_10706.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___225_10706.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___225_10706.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____10730 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____10730 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____10745 =
                            let uu____10746 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____10746 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____10745 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___226_10749 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___226_10749.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___226_10749.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___227_10750 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___227_10750.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___227_10750.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___227_10750.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___227_10750.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___228_10757 = s in
          let uu____10758 =
            let uu____10759 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____10759 in
          {
            FStar_Syntax_Syntax.sigel = uu____10758;
            FStar_Syntax_Syntax.sigrng =
              (uu___228_10757.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___228_10757.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___228_10757.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___228_10757.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____10763 = elim_uvars_aux_t env us [] t in
          (match uu____10763 with
           | (us1,uu____10773,t1) ->
               let uu___229_10781 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___229_10781.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___229_10781.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___229_10781.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___229_10781.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____10782 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____10784 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____10784 with
           | (univs1,binders,signature) ->
               let uu____10800 =
                 let uu____10805 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____10805 with
                 | (univs_opening,univs2) ->
                     let uu____10820 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____10820) in
               (match uu____10800 with
                | (univs_opening,univs_closing) ->
                    let uu____10830 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____10834 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____10835 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____10834, uu____10835) in
                    (match uu____10830 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____10854 =
                           match uu____10854 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____10867 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____10867 with
                                | (us1,t1) ->
                                    let uu____10874 =
                                      let uu____10877 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____10884 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____10877, uu____10884) in
                                    (match uu____10874 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____10895 =
                                           let uu____10898 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____10906 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____10898, uu____10906) in
                                         (match uu____10895 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____10919 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____10919 in
                                              let uu____10920 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____10920 with
                                               | (uu____10931,uu____10932,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____10941 =
                                                       let uu____10942 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____10942 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____10941 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____10947 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____10947 with
                           | (uu____10954,uu____10955,t1) -> t1 in
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
                             | uu____10992 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____11006 =
                               let uu____11007 =
                                 FStar_Syntax_Subst.compress body in
                               uu____11007.FStar_Syntax_Syntax.n in
                             match uu____11006 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____11038 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____11055 =
                               let uu____11056 =
                                 FStar_Syntax_Subst.compress t in
                               uu____11056.FStar_Syntax_Syntax.n in
                             match uu____11055 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____11068) ->
                                 let uu____11079 = destruct_action_body body in
                                 (match uu____11079 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____11103 ->
                                 let uu____11104 = destruct_action_body t in
                                 (match uu____11104 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____11130 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____11130 with
                           | (action_univs,t) ->
                               let uu____11136 = destruct_action_typ_templ t in
                               (match uu____11136 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___230_11159 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___230_11159.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___230_11159.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___231_11161 = ed in
                           let uu____11162 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____11163 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____11164 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____11165 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____11166 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____11167 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____11168 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____11169 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____11170 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____11171 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____11172 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____11173 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____11174 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____11175 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___231_11161.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___231_11161.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____11162;
                             FStar_Syntax_Syntax.bind_wp = uu____11163;
                             FStar_Syntax_Syntax.if_then_else = uu____11164;
                             FStar_Syntax_Syntax.ite_wp = uu____11165;
                             FStar_Syntax_Syntax.stronger = uu____11166;
                             FStar_Syntax_Syntax.close_wp = uu____11167;
                             FStar_Syntax_Syntax.assert_p = uu____11168;
                             FStar_Syntax_Syntax.assume_p = uu____11169;
                             FStar_Syntax_Syntax.null_wp = uu____11170;
                             FStar_Syntax_Syntax.trivial = uu____11171;
                             FStar_Syntax_Syntax.repr = uu____11172;
                             FStar_Syntax_Syntax.return_repr = uu____11173;
                             FStar_Syntax_Syntax.bind_repr = uu____11174;
                             FStar_Syntax_Syntax.actions = uu____11175
                           } in
                         let uu___232_11177 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___232_11177.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___232_11177.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___232_11177.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___232_11177.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___150_11188 =
            match uu___150_11188 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____11203 = elim_uvars_aux_t env us [] t in
                (match uu____11203 with
                 | (us1,uu____11216,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___233_11227 = sub_eff in
            let uu____11228 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____11230 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___233_11227.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___233_11227.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____11228;
              FStar_Syntax_Syntax.lift = uu____11230
            } in
          let uu___234_11232 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___234_11232.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___234_11232.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___234_11232.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___234_11232.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____11240 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____11240 with
           | (univ_names1,binders1,comp1) ->
               let uu___235_11259 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___235_11259.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___235_11259.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___235_11259.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___235_11259.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____11265 -> s