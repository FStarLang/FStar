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
  | PureSubtermsWithinComputations
  | Simplify
  | EraseUniverses
  | AllowUnboundUniverses
  | Reify
  | CompressUvars
  | NoFullNorm
let uu___is_Beta: step -> Prims.bool =
  fun projectee  -> match projectee with | Beta  -> true | uu____12 -> false
let uu___is_Iota: step -> Prims.bool =
  fun projectee  -> match projectee with | Iota  -> true | uu____16 -> false
let uu___is_Zeta: step -> Prims.bool =
  fun projectee  -> match projectee with | Zeta  -> true | uu____20 -> false
let uu___is_Exclude: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____25 -> false
let __proj__Exclude__item___0: step -> step =
  fun projectee  -> match projectee with | Exclude _0 -> _0
let uu___is_WHNF: step -> Prims.bool =
  fun projectee  -> match projectee with | WHNF  -> true | uu____36 -> false
let uu___is_Primops: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____40 -> false
let uu___is_Eager_unfolding: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____44 -> false
let uu___is_Inlining: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____48 -> false
let uu___is_NoDeltaSteps: step -> Prims.bool =
  fun projectee  ->
    match projectee with | NoDeltaSteps  -> true | uu____52 -> false
let uu___is_UnfoldUntil: step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____57 -> false
let __proj__UnfoldUntil__item___0: step -> FStar_Syntax_Syntax.delta_depth =
  fun projectee  -> match projectee with | UnfoldUntil _0 -> _0
let uu___is_PureSubtermsWithinComputations: step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____68 -> false
let uu___is_Simplify: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____72 -> false
let uu___is_EraseUniverses: step -> Prims.bool =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____76 -> false
let uu___is_AllowUnboundUniverses: step -> Prims.bool =
  fun projectee  ->
    match projectee with | AllowUnboundUniverses  -> true | uu____80 -> false
let uu___is_Reify: step -> Prims.bool =
  fun projectee  -> match projectee with | Reify  -> true | uu____84 -> false
let uu___is_CompressUvars: step -> Prims.bool =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____88 -> false
let uu___is_NoFullNorm: step -> Prims.bool =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____92 -> false
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
    match projectee with | Clos _0 -> true | uu____175 -> false
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
    match projectee with | Univ _0 -> true | uu____214 -> false
let __proj__Univ__item___0: closure -> FStar_Syntax_Syntax.universe =
  fun projectee  -> match projectee with | Univ _0 -> _0
let uu___is_Dummy: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____225 -> false
type env = closure Prims.list
let closure_to_string: closure -> Prims.string =
  fun uu___130_229  ->
    match uu___130_229 with
    | Clos (uu____230,t,uu____232,uu____233) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____244 -> "Univ"
    | Dummy  -> "dummy"
type cfg =
  {
  steps: steps;
  tcenv: FStar_TypeChecker_Env.env;
  delta_level: FStar_TypeChecker_Env.delta_level Prims.list;
  primitive_steps: primitive_step Prims.list;}
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
  (env,FStar_Syntax_Syntax.binders,env,(FStar_Syntax_Syntax.lcomp,FStar_Syntax_Syntax.residual_comp)
                                         FStar_Util.either
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
    match projectee with | Arg _0 -> true | uu____371 -> false
let __proj__Arg__item___0:
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Arg _0 -> _0
let uu___is_UnivArgs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____395 -> false
let __proj__UnivArgs__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____419 -> false
let __proj__MemoLazy__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0
let uu___is_Match: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____446 -> false
let __proj__Match__item___0:
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Abs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____475 -> false
let __proj__Abs__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,(FStar_Syntax_Syntax.lcomp,FStar_Syntax_Syntax.residual_comp)
                                           FStar_Util.either
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____514 -> false
let __proj__App__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Meta: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____537 -> false
let __proj__Meta__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Meta _0 -> _0
let uu___is_Let: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____559 -> false
let __proj__Let__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Steps: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Steps _0 -> true | uu____588 -> false
let __proj__Steps__item___0:
  stack_elt ->
    (steps,primitive_step Prims.list,FStar_TypeChecker_Env.delta_level
                                       Prims.list)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Steps _0 -> _0
let uu___is_Debug: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____615 -> false
let __proj__Debug__item___0: stack_elt -> FStar_Syntax_Syntax.term =
  fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list
let mk t r = FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r
let set_memo r t =
  let uu____663 = FStar_ST.read r in
  match uu____663 with
  | FStar_Pervasives_Native.Some uu____668 ->
      failwith "Unexpected set_memo: thunk already evaluated"
  | FStar_Pervasives_Native.None  ->
      FStar_ST.write r (FStar_Pervasives_Native.Some t)
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____677 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____677 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___131_682  ->
    match uu___131_682 with
    | Arg (c,uu____684,uu____685) ->
        let uu____686 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____686
    | MemoLazy uu____687 -> "MemoLazy"
    | Abs (uu____691,bs,uu____693,uu____694,uu____695) ->
        let uu____702 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____702
    | UnivArgs uu____707 -> "UnivArgs"
    | Match uu____711 -> "Match"
    | App (t,uu____716,uu____717) ->
        let uu____718 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____718
    | Meta (m,uu____720) -> "Meta"
    | Let uu____721 -> "Let"
    | Steps (uu____726,uu____727,uu____728) -> "Steps"
    | Debug t ->
        let uu____734 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____734
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____740 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____740 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____754 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____754 then f () else ()
let is_empty uu___132_763 =
  match uu___132_763 with | [] -> true | uu____765 -> false
let lookup_bvar env x =
  try FStar_List.nth env x.FStar_Syntax_Syntax.index
  with
  | uu____783 ->
      let uu____784 =
        let uu____785 = FStar_Syntax_Print.db_to_string x in
        FStar_Util.format1 "Failed to find %s\n" uu____785 in
      failwith uu____784
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
          let uu____816 =
            FStar_List.fold_left
              (fun uu____825  ->
                 fun u1  ->
                   match uu____825 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____840 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____840 with
                        | (k_u,n1) ->
                            let uu____849 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____849
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____816 with
          | (uu____859,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____875 = FStar_List.nth env x in
                 match uu____875 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____878 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____882 ->
                   let uu____883 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____883
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____887 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____890 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____895 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____895 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____906 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____906 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____911 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____914 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____914 with
                                  | (uu____917,m) -> n1 <= m)) in
                        if uu____911 then rest1 else us1
                    | uu____921 -> us1)
               | uu____924 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____927 = aux u3 in
              FStar_List.map (fun _0_30  -> FStar_Syntax_Syntax.U_succ _0_30)
                uu____927 in
        let uu____929 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____929
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____931 = aux u in
           match uu____931 with
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
          (fun uu____1028  ->
             let uu____1029 = FStar_Syntax_Print.tag_of_term t in
             let uu____1030 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1029
               uu____1030);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1031 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1034 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____1055 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____1056 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____1057 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____1058 -> t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____1068 =
                    let uu____1069 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____1069 in
                  mk uu____1068 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t2,us) ->
                  let uu____1076 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t2 uu____1076
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____1078 = lookup_bvar env x in
                  (match uu____1078 with
                   | Univ uu____1079 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____1083) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____1151 = closures_as_binders_delayed cfg env bs in
                  (match uu____1151 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____1171 =
                         let uu____1172 =
                           let uu____1187 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____1187) in
                         FStar_Syntax_Syntax.Tm_abs uu____1172 in
                       mk uu____1171 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____1217 = closures_as_binders_delayed cfg env bs in
                  (match uu____1217 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____1248 =
                    let uu____1255 =
                      let uu____1259 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____1259] in
                    closures_as_binders_delayed cfg env uu____1255 in
                  (match uu____1248 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____1273 =
                         let uu____1274 =
                           let uu____1279 =
                             let uu____1280 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____1280
                               FStar_Pervasives_Native.fst in
                           (uu____1279, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____1274 in
                       mk uu____1273 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____1348 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____1348
                    | FStar_Util.Inr c ->
                        let uu____1362 = close_comp cfg env c in
                        FStar_Util.Inr uu____1362 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____1377 =
                    let uu____1378 =
                      let uu____1396 = closure_as_term_delayed cfg env t11 in
                      (uu____1396, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____1378 in
                  mk uu____1377 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____1434 =
                    let uu____1435 =
                      let uu____1440 = closure_as_term_delayed cfg env t' in
                      let uu____1443 =
                        let uu____1444 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____1444 in
                      (uu____1440, uu____1443) in
                    FStar_Syntax_Syntax.Tm_meta uu____1435 in
                  mk uu____1434 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____1486 =
                    let uu____1487 =
                      let uu____1492 = closure_as_term_delayed cfg env t' in
                      let uu____1495 =
                        let uu____1496 =
                          let uu____1501 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____1501) in
                        FStar_Syntax_Syntax.Meta_monadic uu____1496 in
                      (uu____1492, uu____1495) in
                    FStar_Syntax_Syntax.Tm_meta uu____1487 in
                  mk uu____1486 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____1520 =
                    let uu____1521 =
                      let uu____1526 = closure_as_term_delayed cfg env t' in
                      let uu____1529 =
                        let uu____1530 =
                          let uu____1536 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____1536) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____1530 in
                      (uu____1526, uu____1529) in
                    FStar_Syntax_Syntax.Tm_meta uu____1521 in
                  mk uu____1520 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____1549 =
                    let uu____1550 =
                      let uu____1555 = closure_as_term_delayed cfg env t' in
                      (uu____1555, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____1550 in
                  mk uu____1549 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____1576  -> Dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let body1 =
                    match lb.FStar_Syntax_Syntax.lbname with
                    | FStar_Util.Inr uu____1587 -> body
                    | FStar_Util.Inl uu____1588 ->
                        closure_as_term cfg (Dummy :: env0) body in
                  let lb1 =
                    let uu___145_1590 = lb in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___145_1590.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___145_1590.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = typ;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___145_1590.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = def
                    } in
                  mk (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((uu____1597,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____1621  -> fun env2  -> Dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____1626 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____1626
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____1630  -> fun env2  -> Dummy :: env2) lbs
                          env_univs in
                    let uu___146_1633 = lb in
                    let uu____1634 =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let uu____1637 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___146_1633.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___146_1633.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = uu____1634;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___146_1633.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____1637
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____1648  -> fun env1  -> Dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____1703 =
                    match uu____1703 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____1749 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____1765 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____1799  ->
                                        fun uu____1800  ->
                                          match (uu____1799, uu____1800) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____1865 =
                                                norm_pat env3 p1 in
                                              (match uu____1865 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____1765 with
                               | (pats1,env3) ->
                                   ((let uu___147_1931 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.ty =
                                         (uu___147_1931.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___147_1931.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___148_1945 = x in
                                let uu____1946 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___148_1945.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___148_1945.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1946
                                } in
                              ((let uu___149_1952 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___149_1952.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___149_1952.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___150_1957 = x in
                                let uu____1958 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___150_1957.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___150_1957.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1958
                                } in
                              ((let uu___151_1964 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___151_1964.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___151_1964.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___152_1974 = x in
                                let uu____1975 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___152_1974.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___152_1974.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1975
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___153_1982 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___153_1982.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___153_1982.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____1985 = norm_pat env1 pat in
                        (match uu____1985 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____2009 =
                                     closure_as_term cfg env2 w in
                                   FStar_Pervasives_Native.Some uu____2009 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____2014 =
                    let uu____2015 =
                      let uu____2031 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____2031) in
                    FStar_Syntax_Syntax.Tm_match uu____2015 in
                  mk uu____2014 t1.FStar_Syntax_Syntax.pos))
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
        | uu____2084 -> closure_as_term cfg env t
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
        | uu____2100 ->
            FStar_List.map
              (fun uu____2110  ->
                 match uu____2110 with
                 | (x,imp) ->
                     let uu____2125 = closure_as_term_delayed cfg env x in
                     (uu____2125, imp)) args
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
        let uu____2137 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____2161  ->
                  fun uu____2162  ->
                    match (uu____2161, uu____2162) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___154_2206 = b in
                          let uu____2207 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___154_2206.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___154_2206.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____2207
                          } in
                        let env2 = Dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____2137 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____2254 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____2266 = closure_as_term_delayed cfg env t in
                 let uu____2267 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____2266 uu____2267
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____2277 = closure_as_term_delayed cfg env t in
                 let uu____2278 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____2277 uu____2278
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
                        (fun uu___133_2294  ->
                           match uu___133_2294 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____2298 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____2298
                           | f -> f)) in
                 let uu____2302 =
                   let uu___155_2303 = c1 in
                   let uu____2304 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____2304;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___155_2303.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____2302)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.cflags Prims.list =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_List.filter
         (fun uu___134_2308  ->
            match uu___134_2308 with
            | FStar_Syntax_Syntax.DECREASES uu____2309 -> false
            | uu____2312 -> true))
and close_lcomp_opt:
  cfg ->
    closure Prims.list ->
      (FStar_Syntax_Syntax.lcomp,(FStar_Ident.lident,FStar_Syntax_Syntax.cflags
                                                       Prims.list)
                                   FStar_Pervasives_Native.tuple2)
        FStar_Util.either FStar_Pervasives_Native.option ->
        (FStar_Syntax_Syntax.lcomp,(FStar_Ident.lident,FStar_Syntax_Syntax.cflags
                                                         Prims.list)
                                     FStar_Pervasives_Native.tuple2)
          FStar_Util.either FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | FStar_Pervasives_Native.Some (FStar_Util.Inl lc) ->
            let flags = filter_out_lcomp_cflags lc in
            let uu____2340 = FStar_Syntax_Util.is_total_lcomp lc in
            if uu____2340
            then
              FStar_Pervasives_Native.Some
                (FStar_Util.Inr (FStar_Parser_Const.effect_Tot_lid, flags))
            else
              (let uu____2357 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
               if uu____2357
               then
                 FStar_Pervasives_Native.Some
                   (FStar_Util.Inr
                      (FStar_Parser_Const.effect_GTot_lid, flags))
               else
                 FStar_Pervasives_Native.Some
                   (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags)))
        | uu____2383 -> lopt
let built_in_primitive_steps: primitive_step Prims.list =
  let const_as_tm c p = mk (FStar_Syntax_Syntax.Tm_constant c) p in
  let int_as_const p i =
    let uu____2407 =
      let uu____2408 =
        let uu____2414 = FStar_Util.string_of_int i in
        (uu____2414, FStar_Pervasives_Native.None) in
      FStar_Const.Const_int uu____2408 in
    const_as_tm uu____2407 p in
  let bool_as_const p b = const_as_tm (FStar_Const.Const_bool b) p in
  let string_as_const p b = const_as_tm (FStar_Const.Const_string (b, p)) p in
  let arg_as_int uu____2440 =
    match uu____2440 with
    | (a,uu____2445) ->
        let uu____2447 =
          let uu____2448 = FStar_Syntax_Subst.compress a in
          uu____2448.FStar_Syntax_Syntax.n in
        (match uu____2447 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (i,FStar_Pervasives_Native.None )) ->
             let uu____2458 = FStar_Util.int_of_string i in
             FStar_Pervasives_Native.Some uu____2458
         | uu____2459 -> FStar_Pervasives_Native.None) in
  let arg_as_bounded_int uu____2468 =
    match uu____2468 with
    | (a,uu____2475) ->
        let uu____2479 =
          let uu____2480 = FStar_Syntax_Subst.compress a in
          uu____2480.FStar_Syntax_Syntax.n in
        (match uu____2479 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.tk = uu____2487;
                FStar_Syntax_Syntax.pos = uu____2488;
                FStar_Syntax_Syntax.vars = uu____2489;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.tk
                                                              = uu____2491;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____2492;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____2493;_},uu____2494)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____2525 =
               let uu____2528 = FStar_Util.int_of_string i in
               (fv1, uu____2528) in
             FStar_Pervasives_Native.Some uu____2525
         | uu____2531 -> FStar_Pervasives_Native.None) in
  let arg_as_bool uu____2540 =
    match uu____2540 with
    | (a,uu____2545) ->
        let uu____2547 =
          let uu____2548 = FStar_Syntax_Subst.compress a in
          uu____2548.FStar_Syntax_Syntax.n in
        (match uu____2547 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
             FStar_Pervasives_Native.Some b
         | uu____2553 -> FStar_Pervasives_Native.None) in
  let arg_as_char uu____2560 =
    match uu____2560 with
    | (a,uu____2565) ->
        let uu____2567 =
          let uu____2568 = FStar_Syntax_Subst.compress a in
          uu____2568.FStar_Syntax_Syntax.n in
        (match uu____2567 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
             FStar_Pervasives_Native.Some c
         | uu____2573 -> FStar_Pervasives_Native.None) in
  let arg_as_string uu____2580 =
    match uu____2580 with
    | (a,uu____2585) ->
        let uu____2587 =
          let uu____2588 = FStar_Syntax_Subst.compress a in
          uu____2588.FStar_Syntax_Syntax.n in
        (match uu____2587 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____2593)) -> FStar_Pervasives_Native.Some s
         | uu____2594 -> FStar_Pervasives_Native.None) in
  let arg_as_list f uu____2615 =
    match uu____2615 with
    | (a,uu____2624) ->
        let rec sequence l =
          match l with
          | [] -> FStar_Pervasives_Native.Some []
          | (FStar_Pervasives_Native.None )::uu____2643 ->
              FStar_Pervasives_Native.None
          | (FStar_Pervasives_Native.Some x)::xs ->
              let uu____2653 = sequence xs in
              (match uu____2653 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some xs' ->
                   FStar_Pervasives_Native.Some (x :: xs')) in
        let uu____2664 = FStar_Syntax_Util.list_elements a in
        (match uu____2664 with
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some elts ->
             let uu____2674 =
               FStar_List.map
                 (fun x  ->
                    let uu____2679 = FStar_Syntax_Syntax.as_arg x in
                    f uu____2679) elts in
             sequence uu____2674) in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____2709 = f a in FStar_Pervasives_Native.Some uu____2709
    | uu____2710 -> FStar_Pervasives_Native.None in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____2749 = f a0 a1 in FStar_Pervasives_Native.Some uu____2749
    | uu____2750 -> FStar_Pervasives_Native.None in
  let unary_op as_a f r args =
    let uu____2794 = FStar_List.map as_a args in lift_unary (f r) uu____2794 in
  let binary_op as_a f r args =
    let uu____2844 = FStar_List.map as_a args in lift_binary (f r) uu____2844 in
  let as_primitive_step uu____2861 =
    match uu____2861 with
    | (l,arity,f) ->
        { name = l; arity; strong_reduction_ok = true; interpretation = f } in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  -> fun x  -> let uu____2899 = f x in int_as_const r uu____2899) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2922 = f x y in int_as_const r uu____2922) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  -> fun x  -> let uu____2939 = f x in bool_as_const r uu____2939) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2962 = f x y in bool_as_const r uu____2962) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2985 = f x y in string_as_const r uu____2985) in
  let list_of_string' rng s =
    let name l =
      let uu____2999 =
        let uu____3000 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____3000 in
      mk uu____2999 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____3010 =
      let uu____3012 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____3012 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____3010 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_of_int1 rng i =
    let uu____3034 = FStar_Util.string_of_int i in
    string_as_const rng uu____3034 in
  let string_of_bool1 rng b =
    string_as_const rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____3050 = FStar_Util.string_of_int i in
    string_as_const rng uu____3050 in
  let string_of_bool2 rng b =
    string_as_const rng (if b then "true" else "false") in
  let basic_ops =
    let uu____3069 =
      let uu____3079 =
        let uu____3089 =
          let uu____3099 =
            let uu____3109 =
              let uu____3119 =
                let uu____3129 =
                  let uu____3139 =
                    let uu____3149 =
                      let uu____3159 =
                        let uu____3169 =
                          let uu____3179 =
                            let uu____3189 =
                              let uu____3199 =
                                let uu____3209 =
                                  let uu____3219 =
                                    let uu____3229 =
                                      let uu____3238 =
                                        FStar_Parser_Const.p2l
                                          ["FStar";
                                          "String";
                                          "list_of_string"] in
                                      (uu____3238, (Prims.parse_int "1"),
                                        (unary_op arg_as_string
                                           list_of_string')) in
                                    let uu____3244 =
                                      let uu____3254 =
                                        let uu____3263 =
                                          FStar_Parser_Const.p2l
                                            ["FStar";
                                            "String";
                                            "string_of_list"] in
                                        (uu____3263, (Prims.parse_int "1"),
                                          (unary_op (arg_as_list arg_as_char)
                                             string_of_list')) in
                                      [uu____3254] in
                                    uu____3229 :: uu____3244 in
                                  (FStar_Parser_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_bool string_of_bool2))
                                    :: uu____3219 in
                                (FStar_Parser_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (unary_op arg_as_int string_of_int2)) ::
                                  uu____3209 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____3199 in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____3189 in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____3179 in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____3169 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____3159 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
                      :: uu____3149 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____3139 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____3129 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____3119 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____3109 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____3099 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____3089 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____3079 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____3069 in
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
      let uu____3558 =
        let uu____3559 =
          let uu____3560 = FStar_Syntax_Syntax.as_arg c in [uu____3560] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____3559 in
      uu____3558 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____3584 =
              let uu____3593 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____3593, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____3602  ->
                        fun uu____3603  ->
                          match (uu____3602, uu____3603) with
                          | ((int_to_t1,x),(uu____3614,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____3620 =
              let uu____3630 =
                let uu____3639 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____3639, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____3648  ->
                          fun uu____3649  ->
                            match (uu____3648, uu____3649) with
                            | ((int_to_t1,x),(uu____3660,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____3666 =
                let uu____3676 =
                  let uu____3685 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____3685, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____3694  ->
                            fun uu____3695  ->
                              match (uu____3694, uu____3695) with
                              | ((int_to_t1,x),(uu____3706,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____3676] in
              uu____3630 :: uu____3666 in
            uu____3584 :: uu____3620)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_bool rng args =
    match args with
    | (_typ,uu____3772)::(a1,uu____3774)::(a2,uu____3776)::[] ->
        let uu____3805 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3805 with
         | FStar_Syntax_Util.Equal  ->
             let uu____3807 =
               mk
                 (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_bool true)) rng in
             FStar_Pervasives_Native.Some uu____3807
         | FStar_Syntax_Util.NotEqual  ->
             let uu____3812 =
               mk
                 (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_bool false)) rng in
             FStar_Pervasives_Native.Some uu____3812
         | uu____3817 -> FStar_Pervasives_Native.None)
    | uu____3818 -> failwith "Unexpected number of arguments" in
  let interp_prop r args =
    match args with
    | (_typ,uu____3831)::(a1,uu____3833)::(a2,uu____3835)::[] ->
        let uu____3864 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3864 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___156_3868 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___156_3868.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___156_3868.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___156_3868.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___157_3875 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___157_3875.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___157_3875.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___157_3875.FStar_Syntax_Syntax.vars)
                })
         | uu____3880 -> FStar_Pervasives_Native.None)
    | (_typ,uu____3882)::uu____3883::(a1,uu____3885)::(a2,uu____3887)::[] ->
        let uu____3924 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3924 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___156_3928 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___156_3928.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___156_3928.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___156_3928.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___157_3935 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___157_3935.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___157_3935.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___157_3935.FStar_Syntax_Syntax.vars)
                })
         | uu____3940 -> FStar_Pervasives_Native.None)
    | uu____3941 -> failwith "Unexpected number of arguments" in
  let decidable_equality =
    {
      name = FStar_Parser_Const.op_Eq;
      arity = (Prims.parse_int "3");
      strong_reduction_ok = true;
      interpretation = interp_bool
    } in
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
  [decidable_equality; propositional_equality; hetero_propositional_equality]
let reduce_primops:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      let uu____3952 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops cfg.steps) in
      if uu____3952
      then tm
      else
        (let uu____3954 = FStar_Syntax_Util.head_and_args tm in
         match uu____3954 with
         | (head1,args) ->
             let uu____3980 =
               let uu____3981 = FStar_Syntax_Util.un_uinst head1 in
               uu____3981.FStar_Syntax_Syntax.n in
             (match uu____3980 with
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____3985 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps in
                  (match uu____3985 with
                   | FStar_Pervasives_Native.None  -> tm
                   | FStar_Pervasives_Native.Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then tm
                       else
                         (let uu____3997 =
                            prim_step.interpretation
                              head1.FStar_Syntax_Syntax.pos args in
                          match uu____3997 with
                          | FStar_Pervasives_Native.None  -> tm
                          | FStar_Pervasives_Native.Some reduced -> reduced))
              | uu____4000 -> tm))
let reduce_equality:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___158_4007 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___158_4007.tcenv);
           delta_level = (uu___158_4007.delta_level);
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
        let uu___159_4029 = t in
        {
          FStar_Syntax_Syntax.n = (uu___159_4029.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___159_4029.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___159_4029.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid ->
            FStar_Pervasives_Native.Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid ->
            FStar_Pervasives_Native.Some false
        | uu____4048 -> FStar_Pervasives_Native.None in
      let simplify arg = ((simp_t (FStar_Pervasives_Native.fst arg)), arg) in
      let uu____4075 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps) in
      if uu____4075
      then reduce_primops cfg tm
      else
        (match tm.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.tk = uu____4078;
                     FStar_Syntax_Syntax.pos = uu____4079;
                     FStar_Syntax_Syntax.vars = uu____4080;_},uu____4081);
                FStar_Syntax_Syntax.tk = uu____4082;
                FStar_Syntax_Syntax.pos = uu____4083;
                FStar_Syntax_Syntax.vars = uu____4084;_},args)
             ->
             let uu____4104 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
             if uu____4104
             then
               let uu____4105 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____4105 with
                | (FStar_Pervasives_Native.Some (true ),uu____4138)::
                    (uu____4139,(arg,uu____4141))::[] -> arg
                | (uu____4182,(arg,uu____4184))::(FStar_Pervasives_Native.Some
                                                  (true ),uu____4185)::[]
                    -> arg
                | (FStar_Pervasives_Native.Some (false ),uu____4226)::uu____4227::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____4265::(FStar_Pervasives_Native.Some (false
                               ),uu____4266)::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____4304 -> tm)
             else
               (let uu____4314 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
                if uu____4314
                then
                  let uu____4315 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____4315 with
                  | (FStar_Pervasives_Native.Some (true ),uu____4348)::uu____4349::[]
                      -> w FStar_Syntax_Util.t_true
                  | uu____4387::(FStar_Pervasives_Native.Some (true
                                 ),uu____4388)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____4426)::
                      (uu____4427,(arg,uu____4429))::[] -> arg
                  | (uu____4470,(arg,uu____4472))::(FStar_Pervasives_Native.Some
                                                    (false ),uu____4473)::[]
                      -> arg
                  | uu____4514 -> tm
                else
                  (let uu____4524 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.imp_lid in
                   if uu____4524
                   then
                     let uu____4525 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____4525 with
                     | uu____4558::(FStar_Pervasives_Native.Some (true
                                    ),uu____4559)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____4597)::uu____4598::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____4636)::
                         (uu____4637,(arg,uu____4639))::[] -> arg
                     | uu____4680 -> tm
                   else
                     (let uu____4690 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____4690
                      then
                        let uu____4691 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____4691 with
                        | (FStar_Pervasives_Native.Some (true ),uu____4724)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____4748)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____4772 -> tm
                      else
                        (let uu____4782 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____4782
                         then
                           match args with
                           | (t,uu____4784)::[] ->
                               let uu____4797 =
                                 let uu____4798 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____4798.FStar_Syntax_Syntax.n in
                               (match uu____4797 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____4801::[],body,uu____4803) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____4829 -> tm)
                                | uu____4831 -> tm)
                           | (uu____4832,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____4833))::
                               (t,uu____4835)::[] ->
                               let uu____4862 =
                                 let uu____4863 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____4863.FStar_Syntax_Syntax.n in
                               (match uu____4862 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____4866::[],body,uu____4868) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____4894 -> tm)
                                | uu____4896 -> tm)
                           | uu____4897 -> tm
                         else
                           (let uu____4904 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____4904
                            then
                              match args with
                              | (t,uu____4906)::[] ->
                                  let uu____4919 =
                                    let uu____4920 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____4920.FStar_Syntax_Syntax.n in
                                  (match uu____4919 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____4923::[],body,uu____4925) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____4951 -> tm)
                                   | uu____4953 -> tm)
                              | (uu____4954,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____4955))::
                                  (t,uu____4957)::[] ->
                                  let uu____4984 =
                                    let uu____4985 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____4985.FStar_Syntax_Syntax.n in
                                  (match uu____4984 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____4988::[],body,uu____4990) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____5016 -> tm)
                                   | uu____5018 -> tm)
                              | uu____5019 -> tm
                            else reduce_equality cfg tm)))))
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                FStar_Syntax_Syntax.tk = uu____5027;
                FStar_Syntax_Syntax.pos = uu____5028;
                FStar_Syntax_Syntax.vars = uu____5029;_},args)
             ->
             let uu____5045 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
             if uu____5045
             then
               let uu____5046 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____5046 with
                | (FStar_Pervasives_Native.Some (true ),uu____5079)::
                    (uu____5080,(arg,uu____5082))::[] -> arg
                | (uu____5123,(arg,uu____5125))::(FStar_Pervasives_Native.Some
                                                  (true ),uu____5126)::[]
                    -> arg
                | (FStar_Pervasives_Native.Some (false ),uu____5167)::uu____5168::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____5206::(FStar_Pervasives_Native.Some (false
                               ),uu____5207)::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____5245 -> tm)
             else
               (let uu____5255 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
                if uu____5255
                then
                  let uu____5256 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____5256 with
                  | (FStar_Pervasives_Native.Some (true ),uu____5289)::uu____5290::[]
                      -> w FStar_Syntax_Util.t_true
                  | uu____5328::(FStar_Pervasives_Native.Some (true
                                 ),uu____5329)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____5367)::
                      (uu____5368,(arg,uu____5370))::[] -> arg
                  | (uu____5411,(arg,uu____5413))::(FStar_Pervasives_Native.Some
                                                    (false ),uu____5414)::[]
                      -> arg
                  | uu____5455 -> tm
                else
                  (let uu____5465 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.imp_lid in
                   if uu____5465
                   then
                     let uu____5466 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____5466 with
                     | uu____5499::(FStar_Pervasives_Native.Some (true
                                    ),uu____5500)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____5538)::uu____5539::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____5577)::
                         (uu____5578,(arg,uu____5580))::[] -> arg
                     | uu____5621 -> tm
                   else
                     (let uu____5631 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____5631
                      then
                        let uu____5632 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____5632 with
                        | (FStar_Pervasives_Native.Some (true ),uu____5665)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____5689)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____5713 -> tm
                      else
                        (let uu____5723 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____5723
                         then
                           match args with
                           | (t,uu____5725)::[] ->
                               let uu____5738 =
                                 let uu____5739 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5739.FStar_Syntax_Syntax.n in
                               (match uu____5738 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5742::[],body,uu____5744) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____5770 -> tm)
                                | uu____5772 -> tm)
                           | (uu____5773,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____5774))::
                               (t,uu____5776)::[] ->
                               let uu____5803 =
                                 let uu____5804 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5804.FStar_Syntax_Syntax.n in
                               (match uu____5803 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5807::[],body,uu____5809) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____5835 -> tm)
                                | uu____5837 -> tm)
                           | uu____5838 -> tm
                         else
                           (let uu____5845 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____5845
                            then
                              match args with
                              | (t,uu____5847)::[] ->
                                  let uu____5860 =
                                    let uu____5861 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5861.FStar_Syntax_Syntax.n in
                                  (match uu____5860 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5864::[],body,uu____5866) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____5892 -> tm)
                                   | uu____5894 -> tm)
                              | (uu____5895,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____5896))::
                                  (t,uu____5898)::[] ->
                                  let uu____5925 =
                                    let uu____5926 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5926.FStar_Syntax_Syntax.n in
                                  (match uu____5925 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5929::[],body,uu____5931) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____5957 -> tm)
                                   | uu____5959 -> tm)
                              | uu____5960 -> tm
                            else reduce_equality cfg tm)))))
         | uu____5967 -> tm)
let is_norm_request hd1 args =
  let uu____5982 =
    let uu____5986 =
      let uu____5987 = FStar_Syntax_Util.un_uinst hd1 in
      uu____5987.FStar_Syntax_Syntax.n in
    (uu____5986, args) in
  match uu____5982 with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5992::uu____5993::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5996::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
  | uu____5998 -> false
let get_norm_request args =
  match args with
  | uu____6017::(tm,uu____6019)::[] -> tm
  | (tm,uu____6029)::[] -> tm
  | uu____6034 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___135_6041  ->
    match uu___135_6041 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.tk = uu____6043;
           FStar_Syntax_Syntax.pos = uu____6044;
           FStar_Syntax_Syntax.vars = uu____6045;_},uu____6046,uu____6047))::uu____6048
        -> true
    | uu____6054 -> false
let is_fstar_tactics_embed: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____6059 =
      let uu____6060 = FStar_Syntax_Util.un_uinst t in
      uu____6060.FStar_Syntax_Syntax.n in
    match uu____6059 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Parser_Const.fstar_tactics_embed_lid
    | uu____6064 -> false
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
            (fun uu____6178  ->
               let uu____6179 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____6180 = FStar_Syntax_Print.term_to_string t1 in
               let uu____6181 =
                 let uu____6182 =
                   let uu____6184 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6184 in
                 stack_to_string uu____6182 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____6179
                 uu____6180 uu____6181);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____6196 ->
               failwith "Impossible"
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____6217 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____6226 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____6227 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6228;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____6229;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6234;
                 FStar_Syntax_Syntax.fv_delta = uu____6235;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6239;
                 FStar_Syntax_Syntax.fv_delta = uu____6240;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____6241);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.tk = uu____6249;
                  FStar_Syntax_Syntax.pos = uu____6250;
                  FStar_Syntax_Syntax.vars = uu____6251;_},uu____6252)
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.fstar_tactics_embed_lid
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               is_fstar_tactics_embed hd1 ->
               let args1 = closures_as_args_delayed cfg env args in
               let t2 =
                 let uu___160_6292 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd1, args1));
                   FStar_Syntax_Syntax.tk =
                     (uu___160_6292.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___160_6292.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___160_6292.FStar_Syntax_Syntax.vars)
                 } in
               let t3 = reduce_primops cfg t2 in rebuild cfg env stack1 t3
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____6321 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____6321) && (is_norm_request hd1 args))
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
                 let uu___161_6334 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___161_6334.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___161_6334.primitive_steps)
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
                  FStar_Syntax_Syntax.tk = uu____6339;
                  FStar_Syntax_Syntax.pos = uu____6340;
                  FStar_Syntax_Syntax.vars = uu____6341;_},a1::a2::rest)
               ->
               let uu____6375 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6375 with
                | (hd1,uu____6386) ->
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
                    (FStar_Const.Const_reflect uu____6441);
                  FStar_Syntax_Syntax.tk = uu____6442;
                  FStar_Syntax_Syntax.pos = uu____6443;
                  FStar_Syntax_Syntax.vars = uu____6444;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____6467 = FStar_List.tl stack1 in
               norm cfg env uu____6467 (FStar_Pervasives_Native.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.tk = uu____6470;
                  FStar_Syntax_Syntax.pos = uu____6471;
                  FStar_Syntax_Syntax.vars = uu____6472;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____6495 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6495 with
                | (reify_head,uu____6506) ->
                    let a1 =
                      let uu____6522 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (FStar_Pervasives_Native.fst a) in
                      FStar_Syntax_Subst.compress uu____6522 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____6525);
                            FStar_Syntax_Syntax.tk = uu____6526;
                            FStar_Syntax_Syntax.pos = uu____6527;
                            FStar_Syntax_Syntax.vars = uu____6528;_},a2::[])
                         ->
                         norm cfg env stack1 (FStar_Pervasives_Native.fst a2)
                     | uu____6553 ->
                         let stack2 =
                           (App
                              (reify_head, FStar_Pervasives_Native.None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____6561 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____6561
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____6568 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____6568
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____6571 =
                      let uu____6575 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____6575, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____6571 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___136_6584  ->
                         match uu___136_6584 with
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               if Prims.op_Negation should_delta
               then rebuild cfg env stack1 t1
               else
                 (let r_env =
                    let uu____6588 = FStar_Syntax_Syntax.range_of_fv f in
                    FStar_TypeChecker_Env.set_range cfg.tcenv uu____6588 in
                  let uu____6589 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  match uu____6589 with
                  | FStar_Pervasives_Native.None  ->
                      (log cfg
                         (fun uu____6600  ->
                            FStar_Util.print "Tm_fvar case 2\n" []);
                       rebuild cfg env stack1 t1)
                  | FStar_Pervasives_Native.Some (us,t2) ->
                      (log cfg
                         (fun uu____6606  ->
                            let uu____6607 =
                              FStar_Syntax_Print.term_to_string t0 in
                            let uu____6608 =
                              FStar_Syntax_Print.term_to_string t2 in
                            FStar_Util.print2 ">>> Unfolded %s to %s\n"
                              uu____6607 uu____6608);
                       (let t3 =
                          let uu____6610 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 (UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant)) in
                          if uu____6610
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
                          | (UnivArgs (us',uu____6622))::stack2 ->
                              let env1 =
                                FStar_All.pipe_right us'
                                  (FStar_List.fold_left
                                     (fun env1  -> fun u  -> (Univ u) :: env1)
                                     env) in
                              norm cfg env1 stack2 t3
                          | uu____6635 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack1 t3
                          | uu____6636 ->
                              let uu____6637 =
                                let uu____6638 =
                                  FStar_Syntax_Print.lid_to_string
                                    (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                FStar_Util.format1
                                  "Impossible: missing universe instantiation on %s"
                                  uu____6638 in
                              failwith uu____6637
                        else norm cfg env stack1 t3)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____6645 = lookup_bvar env x in
               (match uu____6645 with
                | Univ uu____6646 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____6661 = FStar_ST.read r in
                      (match uu____6661 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____6680  ->
                                 let uu____6681 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____6682 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____6681
                                   uu____6682);
                            (let uu____6683 =
                               let uu____6684 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____6684.FStar_Syntax_Syntax.n in
                             match uu____6683 with
                             | FStar_Syntax_Syntax.Tm_abs uu____6687 ->
                                 norm cfg env2 stack1 t'
                             | uu____6702 -> rebuild cfg env2 stack1 t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____6735)::uu____6736 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____6741)::uu____6742 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____6748,uu____6749))::stack_rest ->
                    (match c with
                     | Univ uu____6752 -> norm cfg (c :: env) stack_rest t1
                     | uu____6753 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____6756::[] ->
                              (match lopt with
                               | FStar_Pervasives_Native.None  when
                                   FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____6769  ->
                                         let uu____6770 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6770);
                                    norm cfg (c :: env) stack_rest body)
                               | FStar_Pervasives_Native.Some (FStar_Util.Inr
                                   (l,cflags)) when
                                   ((FStar_Ident.lid_equals l
                                       FStar_Parser_Const.effect_Tot_lid)
                                      ||
                                      (FStar_Ident.lid_equals l
                                         FStar_Parser_Const.effect_GTot_lid))
                                     ||
                                     (FStar_All.pipe_right cflags
                                        (FStar_Util.for_some
                                           (fun uu___137_6784  ->
                                              match uu___137_6784 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____6785 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____6787  ->
                                         let uu____6788 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6788);
                                    norm cfg (c :: env) stack_rest body)
                               | FStar_Pervasives_Native.Some (FStar_Util.Inl
                                   lc) when
                                   FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                                   ->
                                   (log cfg
                                      (fun uu____6799  ->
                                         let uu____6800 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6800);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____6801 when
                                   FStar_All.pipe_right cfg.steps
                                     (FStar_List.contains Reify)
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____6808 ->
                                   let cfg1 =
                                     let uu___162_6816 = cfg in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___162_6816.tcenv);
                                       delta_level =
                                         (uu___162_6816.delta_level);
                                       primitive_steps =
                                         (uu___162_6816.primitive_steps)
                                     } in
                                   let uu____6817 =
                                     closure_as_term cfg1 env t1 in
                                   rebuild cfg1 env stack1 uu____6817)
                          | uu____6818::tl1 ->
                              (log cfg
                                 (fun uu____6828  ->
                                    let uu____6829 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____6829);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___163_6853 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___163_6853.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____6866  ->
                          let uu____6867 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____6867);
                     norm cfg env stack2 t1)
                | (Debug uu____6868)::uu____6869 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____6871 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____6871
                    else
                      (let uu____6873 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____6873 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some (FStar_Util.Inl
                                 l) ->
                                 let uu____6902 =
                                   let uu____6908 =
                                     let uu____6909 =
                                       let uu____6910 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____6910 in
                                     FStar_All.pipe_right uu____6909
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____6908
                                     (fun _0_31  -> FStar_Util.Inl _0_31) in
                                 FStar_All.pipe_right uu____6902
                                   (fun _0_32  ->
                                      FStar_Pervasives_Native.Some _0_32)
                             | uu____6935 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____6949  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____6954  ->
                                 let uu____6955 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____6955);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___164_6965 = cfg in
                               let uu____6966 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___164_6965.steps);
                                 tcenv = (uu___164_6965.tcenv);
                                 delta_level = (uu___164_6965.delta_level);
                                 primitive_steps = uu____6966
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____6976)::uu____6977 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____6981 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____6981
                    else
                      (let uu____6983 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____6983 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some (FStar_Util.Inl
                                 l) ->
                                 let uu____7012 =
                                   let uu____7018 =
                                     let uu____7019 =
                                       let uu____7020 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7020 in
                                     FStar_All.pipe_right uu____7019
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7018
                                     (fun _0_33  -> FStar_Util.Inl _0_33) in
                                 FStar_All.pipe_right uu____7012
                                   (fun _0_34  ->
                                      FStar_Pervasives_Native.Some _0_34)
                             | uu____7045 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7059  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7064  ->
                                 let uu____7065 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7065);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___164_7075 = cfg in
                               let uu____7076 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___164_7075.steps);
                                 tcenv = (uu___164_7075.tcenv);
                                 delta_level = (uu___164_7075.delta_level);
                                 primitive_steps = uu____7076
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____7086)::uu____7087 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7093 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7093
                    else
                      (let uu____7095 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7095 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some (FStar_Util.Inl
                                 l) ->
                                 let uu____7124 =
                                   let uu____7130 =
                                     let uu____7131 =
                                       let uu____7132 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7132 in
                                     FStar_All.pipe_right uu____7131
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7130
                                     (fun _0_35  -> FStar_Util.Inl _0_35) in
                                 FStar_All.pipe_right uu____7124
                                   (fun _0_36  ->
                                      FStar_Pervasives_Native.Some _0_36)
                             | uu____7157 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7171  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7176  ->
                                 let uu____7177 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7177);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___164_7187 = cfg in
                               let uu____7188 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___164_7187.steps);
                                 tcenv = (uu___164_7187.tcenv);
                                 delta_level = (uu___164_7187.delta_level);
                                 primitive_steps = uu____7188
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____7198)::uu____7199 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7204 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7204
                    else
                      (let uu____7206 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7206 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some (FStar_Util.Inl
                                 l) ->
                                 let uu____7235 =
                                   let uu____7241 =
                                     let uu____7242 =
                                       let uu____7243 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7243 in
                                     FStar_All.pipe_right uu____7242
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7241
                                     (fun _0_37  -> FStar_Util.Inl _0_37) in
                                 FStar_All.pipe_right uu____7235
                                   (fun _0_38  ->
                                      FStar_Pervasives_Native.Some _0_38)
                             | uu____7268 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7282  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7287  ->
                                 let uu____7288 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7288);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___164_7298 = cfg in
                               let uu____7299 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___164_7298.steps);
                                 tcenv = (uu___164_7298.tcenv);
                                 delta_level = (uu___164_7298.delta_level);
                                 primitive_steps = uu____7299
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____7309)::uu____7310 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7320 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7320
                    else
                      (let uu____7322 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7322 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some (FStar_Util.Inl
                                 l) ->
                                 let uu____7351 =
                                   let uu____7357 =
                                     let uu____7358 =
                                       let uu____7359 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7359 in
                                     FStar_All.pipe_right uu____7358
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7357
                                     (fun _0_39  -> FStar_Util.Inl _0_39) in
                                 FStar_All.pipe_right uu____7351
                                   (fun _0_40  ->
                                      FStar_Pervasives_Native.Some _0_40)
                             | uu____7384 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7398  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7403  ->
                                 let uu____7404 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7404);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___164_7414 = cfg in
                               let uu____7415 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___164_7414.steps);
                                 tcenv = (uu___164_7414.tcenv);
                                 delta_level = (uu___164_7414.delta_level);
                                 primitive_steps = uu____7415
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7425 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7425
                    else
                      (let uu____7427 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7427 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some (FStar_Util.Inl
                                 l) ->
                                 let uu____7456 =
                                   let uu____7462 =
                                     let uu____7463 =
                                       let uu____7464 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7464 in
                                     FStar_All.pipe_right uu____7463
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7462
                                     (fun _0_41  -> FStar_Util.Inl _0_41) in
                                 FStar_All.pipe_right uu____7456
                                   (fun _0_42  ->
                                      FStar_Pervasives_Native.Some _0_42)
                             | uu____7489 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7503  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7508  ->
                                 let uu____7509 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7509);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___164_7519 = cfg in
                               let uu____7520 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___164_7519.steps);
                                 tcenv = (uu___164_7519.tcenv);
                                 delta_level = (uu___164_7519.delta_level);
                                 primitive_steps = uu____7520
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
                      (fun uu____7552  ->
                         fun stack2  ->
                           match uu____7552 with
                           | (a,aq) ->
                               let uu____7560 =
                                 let uu____7561 =
                                   let uu____7565 =
                                     let uu____7566 =
                                       let uu____7576 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____7576, false) in
                                     Clos uu____7566 in
                                   (uu____7565, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____7561 in
                               uu____7560 :: stack2) args) in
               (log cfg
                  (fun uu____7598  ->
                     let uu____7599 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____7599);
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
                             ((let uu___165_7620 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___165_7620.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___165_7620.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____7621 ->
                      let uu____7624 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7624)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____7627 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____7627 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____7643 =
                          let uu____7644 =
                            let uu____7649 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___166_7650 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___166_7650.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___166_7650.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____7649) in
                          FStar_Syntax_Syntax.Tm_refine uu____7644 in
                        mk uu____7643 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____7663 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____7663
               else
                 (let uu____7665 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____7665 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____7671 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  -> fun uu____7677  -> Dummy :: env1)
                               env) in
                        norm_comp cfg uu____7671 c1 in
                      let t2 =
                        let uu____7684 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____7684 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____7727)::uu____7728 -> norm cfg env stack1 t11
                | (Arg uu____7733)::uu____7734 -> norm cfg env stack1 t11
                | (App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.tk = uu____7739;
                       FStar_Syntax_Syntax.pos = uu____7740;
                       FStar_Syntax_Syntax.vars = uu____7741;_},uu____7742,uu____7743))::uu____7744
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____7750)::uu____7751 ->
                    norm cfg env stack1 t11
                | uu____7756 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____7759  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____7772 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____7772
                        | FStar_Util.Inr c ->
                            let uu____7780 = norm_comp cfg env c in
                            FStar_Util.Inr uu____7780 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____7785 =
                        mk
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (t12, (tc1, tacopt1), l))
                          t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____7785)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____7836,{
                              FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                uu____7837;
                              FStar_Syntax_Syntax.lbunivs = uu____7838;
                              FStar_Syntax_Syntax.lbtyp = uu____7839;
                              FStar_Syntax_Syntax.lbeff = uu____7840;
                              FStar_Syntax_Syntax.lbdef = uu____7841;_}::uu____7842),uu____7843)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____7869 =
                 (let uu____7870 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____7870) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____7871 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____7871))) in
               if uu____7869
               then
                 let env1 =
                   let uu____7874 =
                     let uu____7875 =
                       let uu____7885 =
                         FStar_Util.mk_ref FStar_Pervasives_Native.None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____7885,
                         false) in
                     Clos uu____7875 in
                   uu____7874 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____7909 =
                    let uu____7912 =
                      let uu____7913 =
                        let uu____7914 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____7914
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____7913] in
                    FStar_Syntax_Subst.open_term uu____7912 body in
                  match uu____7909 with
                  | (bs,body1) ->
                      let lb1 =
                        let uu___167_7920 = lb in
                        let uu____7921 =
                          let uu____7924 =
                            let uu____7925 = FStar_List.hd bs in
                            FStar_All.pipe_right uu____7925
                              FStar_Pervasives_Native.fst in
                          FStar_All.pipe_right uu____7924
                            (fun _0_43  -> FStar_Util.Inl _0_43) in
                        let uu____7934 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____7937 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = uu____7921;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___167_7920.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____7934;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___167_7920.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____7937
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____7947  -> Dummy :: env1)
                             env) in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____7963 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____7963
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____7976 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____7998  ->
                        match uu____7998 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____8037 =
                                let uu___168_8038 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___168_8038.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___168_8038.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____8037 in
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
               (match uu____7976 with
                | (rec_env,memos,uu____8098) ->
                    let uu____8113 =
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
                             let uu____8155 =
                               let uu____8156 =
                                 let uu____8166 =
                                   FStar_Util.mk_ref
                                     FStar_Pervasives_Native.None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____8166, false) in
                               Clos uu____8156 in
                             uu____8155 :: env1)
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
                             FStar_Syntax_Syntax.tk = uu____8204;
                             FStar_Syntax_Syntax.pos = uu____8205;
                             FStar_Syntax_Syntax.vars = uu____8206;_},uu____8207,uu____8208))::uu____8209
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____8215 -> false in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____8222 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____8222
                        then
                          let uu___169_8223 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___169_8223.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps = (uu___169_8223.primitive_steps)
                          }
                        else
                          (let uu___170_8225 = cfg in
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___170_8225.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta];
                             primitive_steps =
                               (uu___170_8225.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____8227 =
                         let uu____8228 = FStar_Syntax_Subst.compress head1 in
                         uu____8228.FStar_Syntax_Syntax.n in
                       match uu____8227 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____8242 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8242 with
                            | (uu____8243,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____8247 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____8254 =
                                         let uu____8255 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____8255.FStar_Syntax_Syntax.n in
                                       match uu____8254 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____8260,uu____8261))
                                           ->
                                           let uu____8270 =
                                             let uu____8271 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____8271.FStar_Syntax_Syntax.n in
                                           (match uu____8270 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____8276,msrc,uu____8278))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____8287 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____8287
                                            | uu____8288 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____8289 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____8290 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____8290 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___171_8294 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___171_8294.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___171_8294.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___171_8294.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____8295 =
                                            FStar_List.tl stack1 in
                                          let uu____8296 =
                                            let uu____8297 =
                                              let uu____8300 =
                                                let uu____8301 =
                                                  let uu____8309 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____8309) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____8301 in
                                              FStar_Syntax_Syntax.mk
                                                uu____8300 in
                                            uu____8297
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____8295 uu____8296
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____8326 =
                                            let uu____8327 = is_return body in
                                            match uu____8327 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____8330;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____8331;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____8332;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____8337 -> false in
                                          if uu____8326
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
                                             let body2 =
                                               let uu____8357 =
                                                 let uu____8360 =
                                                   let uu____8361 =
                                                     let uu____8376 =
                                                       let uu____8378 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____8378] in
                                                     (uu____8376, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          (FStar_Util.Inr
                                                             (m1, [])))) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____8361 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8360 in
                                               uu____8357
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____8411 =
                                                 let uu____8412 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____8412.FStar_Syntax_Syntax.n in
                                               match uu____8411 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____8418::uu____8419::[])
                                                   ->
                                                   let uu____8425 =
                                                     let uu____8428 =
                                                       let uu____8429 =
                                                         let uu____8434 =
                                                           let uu____8436 =
                                                             let uu____8437 =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____8437 in
                                                           let uu____8438 =
                                                             let uu____8440 =
                                                               let uu____8441
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____8441 in
                                                             [uu____8440] in
                                                           uu____8436 ::
                                                             uu____8438 in
                                                         (bind1, uu____8434) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____8429 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8428 in
                                                   uu____8425
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____8453 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____8459 =
                                                 let uu____8462 =
                                                   let uu____8463 =
                                                     let uu____8473 =
                                                       let uu____8475 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____8476 =
                                                         let uu____8478 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____8479 =
                                                           let uu____8481 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____8482 =
                                                             let uu____8484 =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____8485 =
                                                               let uu____8487
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____8488
                                                                 =
                                                                 let uu____8490
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____8490] in
                                                               uu____8487 ::
                                                                 uu____8488 in
                                                             uu____8484 ::
                                                               uu____8485 in
                                                           uu____8481 ::
                                                             uu____8482 in
                                                         uu____8478 ::
                                                           uu____8479 in
                                                       uu____8475 ::
                                                         uu____8476 in
                                                     (bind_inst, uu____8473) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____8463 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8462 in
                                               uu____8459
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____8502 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____8502 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____8520 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8520 with
                            | (uu____8521,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____8544 =
                                        let uu____8545 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____8545.FStar_Syntax_Syntax.n in
                                      match uu____8544 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____8551) -> t4
                                      | uu____8556 -> head2 in
                                    let uu____8557 =
                                      let uu____8558 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____8558.FStar_Syntax_Syntax.n in
                                    match uu____8557 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____8563 ->
                                        FStar_Pervasives_Native.None in
                                  let uu____8564 = maybe_extract_fv head2 in
                                  match uu____8564 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____8570 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____8570
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____8574 =
                                          maybe_extract_fv head3 in
                                        match uu____8574 with
                                        | FStar_Pervasives_Native.Some
                                            uu____8577 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____8578 ->
                                            FStar_Pervasives_Native.Some
                                              false in
                                      (head3, action_unfolded)
                                  | uu____8581 ->
                                      (head2, FStar_Pervasives_Native.None) in
                                ((let is_arg_impure uu____8592 =
                                    match uu____8592 with
                                    | (e,q) ->
                                        let uu____8597 =
                                          let uu____8598 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____8598.FStar_Syntax_Syntax.n in
                                        (match uu____8597 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____8613 -> false) in
                                  let uu____8614 =
                                    let uu____8615 =
                                      let uu____8619 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____8619 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____8615 in
                                  if uu____8614
                                  then
                                    let uu____8622 =
                                      let uu____8623 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____8623 in
                                    failwith uu____8622
                                  else ());
                                 (let uu____8625 =
                                    maybe_unfold_action head_app in
                                  match uu____8625 with
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
                                      let uu____8660 = FStar_List.tl stack1 in
                                      norm cfg env uu____8660 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____8674 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____8674 in
                           let uu____8675 = FStar_List.tl stack1 in
                           norm cfg env uu____8675 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____8758  ->
                                     match uu____8758 with
                                     | (pat,wopt,tm) ->
                                         let uu____8796 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____8796))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____8822 = FStar_List.tl stack1 in
                           norm cfg env uu____8822 tm
                       | uu____8823 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.tk = uu____8832;
                             FStar_Syntax_Syntax.pos = uu____8833;
                             FStar_Syntax_Syntax.vars = uu____8834;_},uu____8835,uu____8836))::uu____8837
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____8843 -> false in
                    if should_reify
                    then
                      let uu____8844 = FStar_List.tl stack1 in
                      let uu____8845 =
                        let uu____8846 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____8846 in
                      norm cfg env uu____8844 uu____8845
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____8849 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____8849
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___172_8855 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___172_8855.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___172_8855.primitive_steps)
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
                | uu____8857 ->
                    (match stack1 with
                     | uu____8858::uu____8859 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____8863)
                              -> norm cfg env ((Meta (m, r)) :: stack1) head1
                          | FStar_Syntax_Syntax.Meta_pattern args ->
                              let args1 = norm_pattern_args cfg env args in
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_pattern args1),
                                      (t1.FStar_Syntax_Syntax.pos))) ::
                                stack1) head1
                          | uu____8878 -> norm cfg env stack1 head1)
                     | [] ->
                         let head2 = norm cfg env [] head1 in
                         let m1 =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               let uu____8888 =
                                 norm_pattern_args cfg env args in
                               FStar_Syntax_Syntax.Meta_pattern uu____8888
                           | uu____8895 -> m in
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
              let uu____8907 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____8907 with
              | (uu____8908,return_repr) ->
                  let return_inst =
                    let uu____8915 =
                      let uu____8916 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____8916.FStar_Syntax_Syntax.n in
                    match uu____8915 with
                    | FStar_Syntax_Syntax.Tm_uinst (return_tm,uu____8922::[])
                        ->
                        let uu____8928 =
                          let uu____8931 =
                            let uu____8932 =
                              let uu____8937 =
                                let uu____8939 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____8939] in
                              (return_tm, uu____8937) in
                            FStar_Syntax_Syntax.Tm_uinst uu____8932 in
                          FStar_Syntax_Syntax.mk uu____8931 in
                        uu____8928 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____8951 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____8954 =
                    let uu____8957 =
                      let uu____8958 =
                        let uu____8968 =
                          let uu____8970 = FStar_Syntax_Syntax.as_arg t in
                          let uu____8971 =
                            let uu____8973 = FStar_Syntax_Syntax.as_arg e in
                            [uu____8973] in
                          uu____8970 :: uu____8971 in
                        (return_inst, uu____8968) in
                      FStar_Syntax_Syntax.Tm_app uu____8958 in
                    FStar_Syntax_Syntax.mk uu____8957 in
                  uu____8954 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____8986 = FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____8986 with
               | FStar_Pervasives_Native.None  ->
                   let uu____8988 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____8988
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____8989;
                     FStar_TypeChecker_Env.mtarget = uu____8990;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____8991;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____9002;
                     FStar_TypeChecker_Env.mtarget = uu____9003;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____9004;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____9022 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____9022)
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
                (fun uu____9052  ->
                   match uu____9052 with
                   | (a,imp) ->
                       let uu____9059 = norm cfg env [] a in
                       (uu____9059, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___173_9074 = comp1 in
            let uu____9077 =
              let uu____9078 =
                let uu____9084 = norm cfg env [] t in
                let uu____9085 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____9084, uu____9085) in
              FStar_Syntax_Syntax.Total uu____9078 in
            {
              FStar_Syntax_Syntax.n = uu____9077;
              FStar_Syntax_Syntax.tk = (uu___173_9074.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___173_9074.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___173_9074.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___174_9100 = comp1 in
            let uu____9103 =
              let uu____9104 =
                let uu____9110 = norm cfg env [] t in
                let uu____9111 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____9110, uu____9111) in
              FStar_Syntax_Syntax.GTotal uu____9104 in
            {
              FStar_Syntax_Syntax.n = uu____9103;
              FStar_Syntax_Syntax.tk = (uu___174_9100.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___174_9100.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___174_9100.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____9142  ->
                      match uu____9142 with
                      | (a,i) ->
                          let uu____9149 = norm cfg env [] a in
                          (uu____9149, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___138_9154  ->
                      match uu___138_9154 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____9158 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____9158
                      | f -> f)) in
            let uu___175_9162 = comp1 in
            let uu____9165 =
              let uu____9166 =
                let uu___176_9167 = ct in
                let uu____9168 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____9169 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____9172 = norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____9168;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___176_9167.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____9169;
                  FStar_Syntax_Syntax.effect_args = uu____9172;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____9166 in
            {
              FStar_Syntax_Syntax.n = uu____9165;
              FStar_Syntax_Syntax.tk = (uu___175_9162.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___175_9162.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___175_9162.FStar_Syntax_Syntax.vars)
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
            (let uu___177_9189 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___177_9189.tcenv);
               delta_level = (uu___177_9189.delta_level);
               primitive_steps = (uu___177_9189.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____9194 = norm1 t in
          FStar_Syntax_Util.non_informative uu____9194 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____9197 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___178_9211 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.tk = (uu___178_9211.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___178_9211.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___178_9211.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____9221 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____9221
            then
              let ct1 =
                match downgrade_ghost_effect_name
                        ct.FStar_Syntax_Syntax.effect_name
                with
                | FStar_Pervasives_Native.Some pure_eff ->
                    let uu___179_9226 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___179_9226.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___179_9226.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___179_9226.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___179_9226.FStar_Syntax_Syntax.flags)
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___180_9228 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___180_9228.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___180_9228.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___180_9228.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___180_9228.FStar_Syntax_Syntax.flags)
                    } in
              let uu___181_9229 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.tk =
                  (uu___181_9229.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___181_9229.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___181_9229.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____9235 -> c
and norm_binder:
  cfg ->
    env ->
      FStar_Syntax_Syntax.binder ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
          FStar_Pervasives_Native.tuple2
  =
  fun cfg  ->
    fun env  ->
      fun uu____9238  ->
        match uu____9238 with
        | (x,imp) ->
            let uu____9241 =
              let uu___182_9242 = x in
              let uu____9243 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___182_9242.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___182_9242.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____9243
              } in
            (uu____9241, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____9249 =
          FStar_List.fold_left
            (fun uu____9256  ->
               fun b  ->
                 match uu____9256 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____9249 with | (nbs,uu____9273) -> FStar_List.rev nbs
and norm_lcomp_opt:
  cfg ->
    env ->
      (FStar_Syntax_Syntax.lcomp,FStar_Syntax_Syntax.residual_comp)
        FStar_Util.either FStar_Pervasives_Native.option ->
        (FStar_Syntax_Syntax.lcomp,FStar_Syntax_Syntax.residual_comp)
          FStar_Util.either FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | FStar_Pervasives_Native.Some (FStar_Util.Inl lc) ->
            let flags = filter_out_lcomp_cflags lc in
            let uu____9290 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
            if uu____9290
            then
              let t = norm cfg env [] lc.FStar_Syntax_Syntax.res_typ in
              let uu____9295 = FStar_Syntax_Util.is_total_lcomp lc in
              (if uu____9295
               then
                 let uu____9299 =
                   let uu____9302 =
                     let uu____9303 =
                       let uu____9306 = FStar_Syntax_Syntax.mk_Total t in
                       FStar_Syntax_Util.comp_set_flags uu____9306 flags in
                     FStar_Syntax_Util.lcomp_of_comp uu____9303 in
                   FStar_Util.Inl uu____9302 in
                 FStar_Pervasives_Native.Some uu____9299
               else
                 (let uu____9310 =
                    let uu____9313 =
                      let uu____9314 =
                        let uu____9317 = FStar_Syntax_Syntax.mk_GTotal t in
                        FStar_Syntax_Util.comp_set_flags uu____9317 flags in
                      FStar_Syntax_Util.lcomp_of_comp uu____9314 in
                    FStar_Util.Inl uu____9313 in
                  FStar_Pervasives_Native.Some uu____9310))
            else
              FStar_Pervasives_Native.Some
                (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags))
        | uu____9330 -> lopt
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
              ((let uu____9342 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____9342
                then
                  let uu____9343 = FStar_Syntax_Print.term_to_string tm in
                  let uu____9344 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2 "Normalized %s to %s\n" uu____9343
                    uu____9344
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___183_9355 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___183_9355.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____9375  ->
                    let uu____9376 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____9376);
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
              let uu____9413 =
                let uu___184_9414 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___184_9414.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___184_9414.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___184_9414.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____9413
          | (Arg (Univ uu____9419,uu____9420,uu____9421))::uu____9422 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____9424,uu____9425))::uu____9426 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____9438),aq,r))::stack2 ->
              (log cfg
                 (fun uu____9454  ->
                    let uu____9455 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____9455);
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
                 (let uu____9466 = FStar_ST.read m in
                  match uu____9466 with
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
                  | FStar_Pervasives_Native.Some (uu____9492,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq)
                          FStar_Pervasives_Native.None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 =
                FStar_Syntax_Syntax.extend_app head1 (t, aq)
                  FStar_Pervasives_Native.None r in
              let uu____9514 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____9514
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____9521  ->
                    let uu____9522 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____9522);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____9527 =
                  log cfg
                    (fun uu____9529  ->
                       let uu____9530 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____9531 =
                         let uu____9532 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____9539  ->
                                   match uu____9539 with
                                   | (p,uu____9545,uu____9546) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____9532
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____9530 uu____9531);
                  (let whnf = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___139_9556  ->
                               match uu___139_9556 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____9557 -> false)) in
                     let steps' =
                       let uu____9560 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____9560
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___185_9563 = cfg in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___185_9563.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___185_9563.primitive_steps)
                     } in
                   let norm_or_whnf env2 t1 =
                     if whnf
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____9597 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____9613 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____9647  ->
                                   fun uu____9648  ->
                                     match (uu____9647, uu____9648) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____9713 = norm_pat env3 p1 in
                                         (match uu____9713 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____9613 with
                          | (pats1,env3) ->
                              ((let uu___186_9779 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___186_9779.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___186_9779.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___187_9793 = x in
                           let uu____9794 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___187_9793.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___187_9793.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9794
                           } in
                         ((let uu___188_9800 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___188_9800.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___188_9800.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___189_9805 = x in
                           let uu____9806 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___189_9805.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___189_9805.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9806
                           } in
                         ((let uu___190_9812 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___190_9812.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___190_9812.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___191_9822 = x in
                           let uu____9823 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___191_9822.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___191_9822.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9823
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___192_9830 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.ty =
                               (uu___192_9830.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___192_9830.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf -> branches
                     | uu____9834 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____9837 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____9837 with
                                 | (p,wopt,e) ->
                                     let uu____9855 = norm_pat env1 p in
                                     (match uu____9855 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Pervasives_Native.Some w
                                                ->
                                                let uu____9879 =
                                                  norm_or_whnf env2 w in
                                                FStar_Pervasives_Native.Some
                                                  uu____9879 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____9884 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____9884) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____9894) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____9899 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____9900;
                        FStar_Syntax_Syntax.fv_delta = uu____9901;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Data_ctor );_}
                      -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____9905;
                        FStar_Syntax_Syntax.fv_delta = uu____9906;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Record_ctor uu____9907);_}
                      -> true
                  | uu____9914 -> false in
                let guard_when_clause wopt b rest =
                  match wopt with
                  | FStar_Pervasives_Native.None  -> b
                  | FStar_Pervasives_Native.Some w ->
                      let then_branch = b in
                      let else_branch =
                        mk (FStar_Syntax_Syntax.Tm_match (scrutinee, rest)) r in
                      FStar_Syntax_Util.if_then_else w then_branch
                        else_branch in
                let rec matches_pat scrutinee1 p =
                  let scrutinee2 = FStar_Syntax_Util.unmeta scrutinee1 in
                  let uu____10013 =
                    FStar_Syntax_Util.head_and_args scrutinee2 in
                  match uu____10013 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var uu____10045 ->
                           FStar_Util.Inl [scrutinee2]
                       | FStar_Syntax_Syntax.Pat_wild uu____10047 ->
                           FStar_Util.Inl [scrutinee2]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____10049 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____10061 ->
                                let uu____10062 =
                                  let uu____10063 = is_cons head1 in
                                  Prims.op_Negation uu____10063 in
                                FStar_Util.Inr uu____10062)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____10077 =
                             let uu____10078 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____10078.FStar_Syntax_Syntax.n in
                           (match uu____10077 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____10085 ->
                                let uu____10086 =
                                  let uu____10087 = is_cons head1 in
                                  Prims.op_Negation uu____10087 in
                                FStar_Util.Inr uu____10086))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____10121)::rest_a,(p1,uu____10124)::rest_p) ->
                      let uu____10152 = matches_pat t1 p1 in
                      (match uu____10152 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____10166 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____10237 = matches_pat scrutinee1 p1 in
                      (match uu____10237 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____10247  ->
                                 let uu____10248 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____10249 =
                                   let uu____10250 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____10250
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____10248 uu____10249);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____10259 =
                                        let uu____10260 =
                                          let uu____10270 =
                                            FStar_Util.mk_ref
                                              (FStar_Pervasives_Native.Some
                                                 ([], t1)) in
                                          ([], t1, uu____10270, false) in
                                        Clos uu____10260 in
                                      uu____10259 :: env2) env1 s in
                             let uu____10293 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____10293))) in
                let uu____10294 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____10294
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___140_10308  ->
                match uu___140_10308 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | uu____10311 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____10315 -> d in
      {
        steps = s;
        tcenv = e;
        delta_level = d1;
        primitive_steps =
          (FStar_List.append built_in_primitive_steps equality_ops)
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
            let uu___193_10335 = config s e in
            {
              steps = (uu___193_10335.steps);
              tcenv = (uu___193_10335.tcenv);
              delta_level = (uu___193_10335.delta_level);
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
      fun t  -> let uu____10354 = config s e in norm_comp uu____10354 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____10361 = config [] env in norm_universe uu____10361 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun c  ->
      let uu____10368 = config [] env in ghost_to_pure_aux uu____10368 [] c
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
        let uu____10380 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____10380 in
      let uu____10381 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____10381
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___194_10383 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___194_10383.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___194_10383.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____10384  ->
                    let uu____10385 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____10385))
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
            ((let uu____10398 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10398);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____10407 = config [AllowUnboundUniverses] env in
          norm_comp uu____10407 [] c
        with
        | e ->
            ((let uu____10411 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10411);
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
                   let uu____10448 =
                     let uu____10449 =
                       let uu____10454 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____10454) in
                     FStar_Syntax_Syntax.Tm_refine uu____10449 in
                   mk uu____10448 t01.FStar_Syntax_Syntax.pos
               | uu____10459 -> t2)
          | uu____10460 -> t2 in
        aux t
let unfold_whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      normalize [WHNF; UnfoldUntil FStar_Syntax_Syntax.Delta_constant; Beta]
        env t
let reduce_uvar_solutions:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      normalize
        [Beta;
        NoDeltaSteps;
        CompressUvars;
        Exclude Zeta;
        Exclude Iota;
        NoFullNorm] env t
let eta_expand_with_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      fun t_e  ->
        let uu____10482 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____10482 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____10498 ->
                 let uu____10502 = FStar_Syntax_Util.abs_formals e in
                 (match uu____10502 with
                  | (actuals,uu____10513,uu____10514) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____10536 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____10536 with
                         | (binders,args) ->
                             let uu____10546 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             let uu____10549 =
                               let uu____10556 =
                                 FStar_All.pipe_right
                                   (FStar_Syntax_Util.lcomp_of_comp c)
                                   (fun _0_44  -> FStar_Util.Inl _0_44) in
                               FStar_All.pipe_right uu____10556
                                 (fun _0_45  ->
                                    FStar_Pervasives_Native.Some _0_45) in
                             FStar_Syntax_Util.abs binders uu____10546
                               uu____10549)))
let eta_expand:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____10592 =
        let uu____10596 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
        (uu____10596, (t.FStar_Syntax_Syntax.n)) in
      match uu____10592 with
      | (FStar_Pervasives_Native.Some sort,uu____10603) ->
          let uu____10605 = mk sort t.FStar_Syntax_Syntax.pos in
          eta_expand_with_type env t uu____10605
      | (uu____10606,FStar_Syntax_Syntax.Tm_name x) ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____10610 ->
          let uu____10614 = FStar_Syntax_Util.head_and_args t in
          (match uu____10614 with
           | (head1,args) ->
               let uu____10640 =
                 let uu____10641 = FStar_Syntax_Subst.compress head1 in
                 uu____10641.FStar_Syntax_Syntax.n in
               (match uu____10640 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____10644,thead) ->
                    let uu____10658 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____10658 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____10689 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___199_10693 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___199_10693.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___199_10693.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___199_10693.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___199_10693.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___199_10693.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___199_10693.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___199_10693.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___199_10693.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___199_10693.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___199_10693.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___199_10693.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___199_10693.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___199_10693.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___199_10693.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___199_10693.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___199_10693.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___199_10693.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___199_10693.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___199_10693.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___199_10693.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___199_10693.FStar_TypeChecker_Env.qname_and_index)
                                 }) t in
                            match uu____10689 with
                            | (uu____10694,ty,uu____10696) ->
                                eta_expand_with_type env t ty))
                | uu____10697 ->
                    let uu____10698 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___200_10702 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___200_10702.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___200_10702.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___200_10702.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___200_10702.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___200_10702.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___200_10702.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___200_10702.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___200_10702.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___200_10702.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___200_10702.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___200_10702.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___200_10702.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___200_10702.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___200_10702.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___200_10702.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___200_10702.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___200_10702.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___200_10702.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___200_10702.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___200_10702.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___200_10702.FStar_TypeChecker_Env.qname_and_index)
                         }) t in
                    (match uu____10698 with
                     | (uu____10703,ty,uu____10705) ->
                         eta_expand_with_type env t ty)))