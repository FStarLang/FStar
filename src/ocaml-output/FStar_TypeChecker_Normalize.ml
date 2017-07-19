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
    match projectee with | Clos _0 -> true | uu____197 -> false
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
    match projectee with | Univ _0 -> true | uu____263 -> false
let __proj__Univ__item___0: closure -> FStar_Syntax_Syntax.universe =
  fun projectee  -> match projectee with | Univ _0 -> _0
let uu___is_Dummy: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____274 -> false
type env = closure Prims.list
let closure_to_string: closure -> Prims.string =
  fun uu___130_279  ->
    match uu___130_279 with
    | Clos (uu____280,t,uu____282,uu____283) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____304 -> "Univ"
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
    match projectee with | Arg _0 -> true | uu____480 -> false
let __proj__Arg__item___0:
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Arg _0 -> _0
let uu___is_UnivArgs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____516 -> false
let __proj__UnivArgs__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____552 -> false
let __proj__MemoLazy__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0
let uu___is_Match: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____591 -> false
let __proj__Match__item___0:
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Abs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____637 -> false
let __proj__Abs__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,(FStar_Syntax_Syntax.lcomp,FStar_Syntax_Syntax.residual_comp)
                                           FStar_Util.either
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____703 -> false
let __proj__App__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Meta: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____737 -> false
let __proj__Meta__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Meta _0 -> _0
let uu___is_Let: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____769 -> false
let __proj__Let__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Steps: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Steps _0 -> true | uu____815 -> false
let __proj__Steps__item___0:
  stack_elt ->
    (steps,primitive_step Prims.list,FStar_TypeChecker_Env.delta_level
                                       Prims.list)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Steps _0 -> _0
let uu___is_Debug: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____857 -> false
let __proj__Debug__item___0: stack_elt -> FStar_Syntax_Syntax.term =
  fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list
let mk t r = FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r
let set_memo r t =
  let uu____908 = FStar_ST.read r in
  match uu____908 with
  | FStar_Pervasives_Native.Some uu____915 ->
      failwith "Unexpected set_memo: thunk already evaluated"
  | FStar_Pervasives_Native.None  ->
      FStar_ST.write r (FStar_Pervasives_Native.Some t)
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____927 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____927 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___131_934  ->
    match uu___131_934 with
    | Arg (c,uu____936,uu____937) ->
        let uu____938 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____938
    | MemoLazy uu____939 -> "MemoLazy"
    | Abs (uu____946,bs,uu____948,uu____949,uu____950) ->
        let uu____963 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____963
    | UnivArgs uu____968 -> "UnivArgs"
    | Match uu____975 -> "Match"
    | App (t,uu____983,uu____984) ->
        let uu____985 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____985
    | Meta (m,uu____987) -> "Meta"
    | Let uu____988 -> "Let"
    | Steps (uu____997,uu____998,uu____999) -> "Steps"
    | Debug t ->
        let uu____1009 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____1009
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____1017 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____1017 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1033 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____1033 then f () else ()
let is_empty uu___132_1043 =
  match uu___132_1043 with | [] -> true | uu____1046 -> false
let lookup_bvar env x =
  try FStar_List.nth env x.FStar_Syntax_Syntax.index
  with
  | uu____1067 ->
      let uu____1068 =
        let uu____1069 = FStar_Syntax_Print.db_to_string x in
        FStar_Util.format1 "Failed to find %s\n" uu____1069 in
      failwith uu____1068
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
          let uu____1110 =
            FStar_List.fold_left
              (fun uu____1127  ->
                 fun u1  ->
                   match uu____1127 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____1152 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____1152 with
                        | (k_u,n1) ->
                            let uu____1167 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____1167
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____1110 with
          | (uu____1185,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____1207 = FStar_List.nth env x in
                 match uu____1207 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____1211 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____1217 ->
                   let uu____1218 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____1218
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1224 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1229 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1236 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____1236 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____1253 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____1253 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____1261 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____1265 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____1265 with
                                  | (uu____1270,m) -> n1 <= m)) in
                        if uu____1261 then rest1 else us1
                    | uu____1275 -> us1)
               | uu____1280 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1284 = aux u3 in
              FStar_List.map (fun _0_30  -> FStar_Syntax_Syntax.U_succ _0_30)
                uu____1284 in
        let uu____1287 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____1287
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1289 = aux u in
           match uu____1289 with
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
          (fun uu____1436  ->
             let uu____1437 = FStar_Syntax_Print.tag_of_term t in
             let uu____1438 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1437
               uu____1438);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1439 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1443 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____1482 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____1483 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____1484 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____1485 -> t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____1503 =
                    let uu____1504 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____1504 in
                  mk uu____1503 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t2,us) ->
                  let uu____1515 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t2 uu____1515
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____1517 = lookup_bvar env x in
                  (match uu____1517 with
                   | Univ uu____1518 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____1522) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____1650 = closures_as_binders_delayed cfg env bs in
                  (match uu____1650 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____1686 =
                         let uu____1687 =
                           let uu____1716 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____1716) in
                         FStar_Syntax_Syntax.Tm_abs uu____1687 in
                       mk uu____1686 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____1773 = closures_as_binders_delayed cfg env bs in
                  (match uu____1773 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____1829 =
                    let uu____1842 =
                      let uu____1849 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____1849] in
                    closures_as_binders_delayed cfg env uu____1842 in
                  (match uu____1829 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____1873 =
                         let uu____1874 =
                           let uu____1883 =
                             let uu____1884 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____1884
                               FStar_Pervasives_Native.fst in
                           (uu____1883, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____1874 in
                       mk uu____1873 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____2013 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____2013
                    | FStar_Util.Inr c ->
                        let uu____2039 = close_comp cfg env c in
                        FStar_Util.Inr uu____2039 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____2067 =
                    let uu____2068 =
                      let uu____2103 = closure_as_term_delayed cfg env t11 in
                      (uu____2103, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____2068 in
                  mk uu____2067 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____2176 =
                    let uu____2177 =
                      let uu____2186 = closure_as_term_delayed cfg env t' in
                      let uu____2191 =
                        let uu____2192 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____2192 in
                      (uu____2186, uu____2191) in
                    FStar_Syntax_Syntax.Tm_meta uu____2177 in
                  mk uu____2176 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____2272 =
                    let uu____2273 =
                      let uu____2282 = closure_as_term_delayed cfg env t' in
                      let uu____2287 =
                        let uu____2288 =
                          let uu____2297 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____2297) in
                        FStar_Syntax_Syntax.Meta_monadic uu____2288 in
                      (uu____2282, uu____2287) in
                    FStar_Syntax_Syntax.Tm_meta uu____2273 in
                  mk uu____2272 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____2330 =
                    let uu____2331 =
                      let uu____2340 = closure_as_term_delayed cfg env t' in
                      let uu____2345 =
                        let uu____2346 =
                          let uu____2357 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____2357) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____2346 in
                      (uu____2340, uu____2345) in
                    FStar_Syntax_Syntax.Tm_meta uu____2331 in
                  mk uu____2330 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____2380 =
                    let uu____2381 =
                      let uu____2390 = closure_as_term_delayed cfg env t' in
                      (uu____2390, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____2381 in
                  mk uu____2380 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____2426  -> Dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let body1 =
                    match lb.FStar_Syntax_Syntax.lbname with
                    | FStar_Util.Inr uu____2444 -> body
                    | FStar_Util.Inl uu____2445 ->
                        closure_as_term cfg (Dummy :: env0) body in
                  let lb1 =
                    let uu___145_2447 = lb in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___145_2447.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___145_2447.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = typ;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___145_2447.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = def
                    } in
                  mk (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((uu____2460,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____2497  -> fun env2  -> Dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____2504 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2504
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____2510  -> fun env2  -> Dummy :: env2) lbs
                          env_univs in
                    let uu___146_2514 = lb in
                    let uu____2515 =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let uu____2520 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___146_2514.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___146_2514.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = uu____2515;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___146_2514.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____2520
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____2538  -> fun env1  -> Dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____2637 =
                    match uu____2637 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____2718 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____2747 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____2814  ->
                                        fun uu____2815  ->
                                          match (uu____2814, uu____2815) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____2940 =
                                                norm_pat env3 p1 in
                                              (match uu____2940 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____2747 with
                               | (pats1,env3) ->
                                   ((let uu___147_3067 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.ty =
                                         (uu___147_3067.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___147_3067.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___148_3092 = x in
                                let uu____3093 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___148_3092.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___148_3092.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3093
                                } in
                              ((let uu___149_3104 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___149_3104.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___149_3104.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___150_3111 = x in
                                let uu____3112 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___150_3111.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___150_3111.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3112
                                } in
                              ((let uu___151_3123 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___151_3123.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___151_3123.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___152_3139 = x in
                                let uu____3140 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___152_3139.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___152_3139.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3140
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___153_3152 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___153_3152.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___153_3152.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____3157 = norm_pat env1 pat in
                        (match uu____3157 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3200 =
                                     closure_as_term cfg env2 w in
                                   FStar_Pervasives_Native.Some uu____3200 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____3208 =
                    let uu____3209 =
                      let uu____3240 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____3240) in
                    FStar_Syntax_Syntax.Tm_match uu____3209 in
                  mk uu____3208 t1.FStar_Syntax_Syntax.pos))
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
        | uu____3342 -> closure_as_term cfg env t
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
        | uu____3370 ->
            FStar_List.map
              (fun uu____3389  ->
                 match uu____3389 with
                 | (x,imp) ->
                     let uu____3416 = closure_as_term_delayed cfg env x in
                     (uu____3416, imp)) args
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
        let uu____3436 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____3483  ->
                  fun uu____3484  ->
                    match (uu____3483, uu____3484) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___154_3566 = b in
                          let uu____3567 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___154_3566.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___154_3566.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____3567
                          } in
                        let env2 = Dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____3436 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____3654 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____3675 = closure_as_term_delayed cfg env t in
                 let uu____3676 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____3675 uu____3676
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____3693 = closure_as_term_delayed cfg env t in
                 let uu____3694 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____3693 uu____3694
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
                        (fun uu___133_3721  ->
                           match uu___133_3721 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____3727 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____3727
                           | f -> f)) in
                 let uu____3733 =
                   let uu___155_3734 = c1 in
                   let uu____3735 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____3735;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___155_3734.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____3733)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.cflags Prims.list =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_List.filter
         (fun uu___134_3741  ->
            match uu___134_3741 with
            | FStar_Syntax_Syntax.DECREASES uu____3742 -> false
            | uu____3747 -> true))
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
            let uu____3797 = FStar_Syntax_Util.is_total_lcomp lc in
            if uu____3797
            then
              FStar_Pervasives_Native.Some
                (FStar_Util.Inr (FStar_Parser_Const.effect_Tot_lid, flags))
            else
              (let uu____3829 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
               if uu____3829
               then
                 FStar_Pervasives_Native.Some
                   (FStar_Util.Inr
                      (FStar_Parser_Const.effect_GTot_lid, flags))
               else
                 FStar_Pervasives_Native.Some
                   (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags)))
        | uu____3879 -> lopt
let built_in_primitive_steps: primitive_step Prims.list =
  let const_as_tm c p = mk (FStar_Syntax_Syntax.Tm_constant c) p in
  let int_as_const p i =
    let uu____3912 =
      let uu____3913 =
        let uu____3924 = FStar_Util.string_of_int i in
        (uu____3924, FStar_Pervasives_Native.None) in
      FStar_Const.Const_int uu____3913 in
    const_as_tm uu____3912 p in
  let bool_as_const p b = const_as_tm (FStar_Const.Const_bool b) p in
  let string_as_const p b =
    const_as_tm
      (FStar_Const.Const_string ((FStar_Util.bytes_of_string b), p)) p in
  let arg_as_int uu____3960 =
    match uu____3960 with
    | (a,uu____3968) ->
        let uu____3971 =
          let uu____3972 = FStar_Syntax_Subst.compress a in
          uu____3972.FStar_Syntax_Syntax.n in
        (match uu____3971 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (i,FStar_Pervasives_Native.None )) ->
             let uu____3990 = FStar_Util.int_of_string i in
             FStar_Pervasives_Native.Some uu____3990
         | uu____3991 -> FStar_Pervasives_Native.None) in
  let arg_as_bounded_int uu____4005 =
    match uu____4005 with
    | (a,uu____4017) ->
        let uu____4024 =
          let uu____4025 = FStar_Syntax_Subst.compress a in
          uu____4025.FStar_Syntax_Syntax.n in
        (match uu____4024 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.tk = uu____4037;
                FStar_Syntax_Syntax.pos = uu____4038;
                FStar_Syntax_Syntax.vars = uu____4039;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.tk
                                                              = uu____4041;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____4042;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____4043;_},uu____4044)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____4101 =
               let uu____4106 = FStar_Util.int_of_string i in
               (fv1, uu____4106) in
             FStar_Pervasives_Native.Some uu____4101
         | uu____4111 -> FStar_Pervasives_Native.None) in
  let arg_as_bool uu____4125 =
    match uu____4125 with
    | (a,uu____4133) ->
        let uu____4136 =
          let uu____4137 = FStar_Syntax_Subst.compress a in
          uu____4137.FStar_Syntax_Syntax.n in
        (match uu____4136 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
             FStar_Pervasives_Native.Some b
         | uu____4145 -> FStar_Pervasives_Native.None) in
  let arg_as_char uu____4155 =
    match uu____4155 with
    | (a,uu____4163) ->
        let uu____4166 =
          let uu____4167 = FStar_Syntax_Subst.compress a in
          uu____4167.FStar_Syntax_Syntax.n in
        (match uu____4166 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
             FStar_Pervasives_Native.Some c
         | uu____4175 -> FStar_Pervasives_Native.None) in
  let arg_as_string uu____4185 =
    match uu____4185 with
    | (a,uu____4193) ->
        let uu____4196 =
          let uu____4197 = FStar_Syntax_Subst.compress a in
          uu____4197.FStar_Syntax_Syntax.n in
        (match uu____4196 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (bytes,uu____4205)) ->
             FStar_Pervasives_Native.Some (FStar_Util.string_of_bytes bytes)
         | uu____4210 -> FStar_Pervasives_Native.None) in
  let arg_as_list f uu____4236 =
    match uu____4236 with
    | (a,uu____4250) ->
        let rec sequence l =
          match l with
          | [] -> FStar_Pervasives_Native.Some []
          | (FStar_Pervasives_Native.None )::uu____4283 ->
              FStar_Pervasives_Native.None
          | (FStar_Pervasives_Native.Some x)::xs ->
              let uu____4300 = sequence xs in
              (match uu____4300 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some xs' ->
                   FStar_Pervasives_Native.Some (x :: xs')) in
        let uu____4320 = FStar_Syntax_Util.list_elements a in
        (match uu____4320 with
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some elts ->
             let uu____4338 =
               FStar_List.map
                 (fun x  ->
                    let uu____4346 = FStar_Syntax_Syntax.as_arg x in
                    f uu____4346) elts in
             sequence uu____4338) in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4384 = f a in FStar_Pervasives_Native.Some uu____4384
    | uu____4385 -> FStar_Pervasives_Native.None in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4435 = f a0 a1 in FStar_Pervasives_Native.Some uu____4435
    | uu____4436 -> FStar_Pervasives_Native.None in
  let unary_op as_a f r args =
    let uu____4485 = FStar_List.map as_a args in lift_unary (f r) uu____4485 in
  let binary_op as_a f r args =
    let uu____4541 = FStar_List.map as_a args in lift_binary (f r) uu____4541 in
  let as_primitive_step uu____4565 =
    match uu____4565 with
    | (l,arity,f) ->
        { name = l; arity; strong_reduction_ok = true; interpretation = f } in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  -> fun x  -> let uu____4610 = f x in int_as_const r uu____4610) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  -> let uu____4634 = f x y in int_as_const r uu____4634) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  -> fun x  -> let uu____4652 = f x in bool_as_const r uu____4652) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  -> let uu____4676 = f x y in bool_as_const r uu____4676) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  -> let uu____4700 = f x y in string_as_const r uu____4700) in
  let list_of_string' rng s =
    let name l =
      let uu____4716 =
        let uu____4717 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____4717 in
      mk uu____4716 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____4731 =
      let uu____4734 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____4734 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____4731 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_of_int1 rng i =
    let uu____4762 = FStar_Util.string_of_int i in
    string_as_const rng uu____4762 in
  let string_of_bool1 rng b =
    string_as_const rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____4778 = FStar_Util.string_of_int i in
    string_as_const rng uu____4778 in
  let string_of_bool2 rng b =
    string_as_const rng (if b then "true" else "false") in
  let basic_ops =
    let uu____4802 =
      let uu____4817 =
        let uu____4832 =
          let uu____4847 =
            let uu____4862 =
              let uu____4877 =
                let uu____4892 =
                  let uu____4907 =
                    let uu____4922 =
                      let uu____4937 =
                        let uu____4952 =
                          let uu____4967 =
                            let uu____4982 =
                              let uu____4997 =
                                let uu____5012 =
                                  let uu____5027 =
                                    let uu____5042 =
                                      let uu____5055 =
                                        FStar_Parser_Const.p2l
                                          ["FStar";
                                          "String";
                                          "list_of_string"] in
                                      (uu____5055, (Prims.parse_int "1"),
                                        (unary_op arg_as_string
                                           list_of_string')) in
                                    let uu____5062 =
                                      let uu____5077 =
                                        let uu____5090 =
                                          FStar_Parser_Const.p2l
                                            ["FStar";
                                            "String";
                                            "string_of_list"] in
                                        (uu____5090, (Prims.parse_int "1"),
                                          (unary_op (arg_as_list arg_as_char)
                                             string_of_list')) in
                                      [uu____5077] in
                                    uu____5042 :: uu____5062 in
                                  (FStar_Parser_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_bool string_of_bool2))
                                    :: uu____5027 in
                                (FStar_Parser_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (unary_op arg_as_int string_of_int2)) ::
                                  uu____5012 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____4997 in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____4982 in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____4967 in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____4952 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____4937 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
                      :: uu____4922 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____4907 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____4892 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____4877 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____4862 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____4847 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____4832 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____4817 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____4802 in
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
      let uu____5487 =
        let uu____5488 =
          let uu____5489 = FStar_Syntax_Syntax.as_arg c in [uu____5489] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____5488 in
      uu____5487 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____5521 =
              let uu____5534 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____5534, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____5546  ->
                        fun uu____5547  ->
                          match (uu____5546, uu____5547) with
                          | ((int_to_t1,x),(uu____5566,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____5576 =
              let uu____5591 =
                let uu____5604 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____5604, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____5616  ->
                          fun uu____5617  ->
                            match (uu____5616, uu____5617) with
                            | ((int_to_t1,x),(uu____5636,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____5646 =
                let uu____5661 =
                  let uu____5674 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____5674, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____5686  ->
                            fun uu____5687  ->
                              match (uu____5686, uu____5687) with
                              | ((int_to_t1,x),(uu____5706,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____5661] in
              uu____5591 :: uu____5646 in
            uu____5521 :: uu____5576)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_bool rng args =
    match args with
    | (_typ,uu____5804)::(a1,uu____5806)::(a2,uu____5808)::[] ->
        let uu____5865 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____5865 with
         | FStar_Syntax_Util.Equal  ->
             let uu____5868 =
               mk
                 (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_bool true)) rng in
             FStar_Pervasives_Native.Some uu____5868
         | FStar_Syntax_Util.NotEqual  ->
             let uu____5877 =
               mk
                 (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_bool false)) rng in
             FStar_Pervasives_Native.Some uu____5877
         | uu____5886 -> FStar_Pervasives_Native.None)
    | uu____5887 -> failwith "Unexpected number of arguments" in
  let interp_prop r args =
    match args with
    | (_typ,uu____5904)::(a1,uu____5906)::(a2,uu____5908)::[] ->
        let uu____5965 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____5965 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___156_5972 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___156_5972.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___156_5972.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___156_5972.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___157_5977 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___157_5977.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___157_5977.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___157_5977.FStar_Syntax_Syntax.vars)
                })
         | uu____5978 -> FStar_Pervasives_Native.None)
    | (_typ,uu____5980)::uu____5981::(a1,uu____5983)::(a2,uu____5985)::[] ->
        let uu____6058 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6058 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___156_6065 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___156_6065.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___156_6065.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___156_6065.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___157_6070 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___157_6070.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___157_6070.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___157_6070.FStar_Syntax_Syntax.vars)
                })
         | uu____6071 -> FStar_Pervasives_Native.None)
    | uu____6072 -> failwith "Unexpected number of arguments" in
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
      let uu____6084 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops cfg.steps) in
      if uu____6084
      then tm
      else
        (let uu____6086 = FStar_Syntax_Util.head_and_args tm in
         match uu____6086 with
         | (head1,args) ->
             let uu____6135 =
               let uu____6136 = FStar_Syntax_Util.un_uinst head1 in
               uu____6136.FStar_Syntax_Syntax.n in
             (match uu____6135 with
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____6142 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps in
                  (match uu____6142 with
                   | FStar_Pervasives_Native.None  -> tm
                   | FStar_Pervasives_Native.Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then tm
                       else
                         (let uu____6156 =
                            prim_step.interpretation
                              head1.FStar_Syntax_Syntax.pos args in
                          match uu____6156 with
                          | FStar_Pervasives_Native.None  -> tm
                          | FStar_Pervasives_Native.Some reduced -> reduced))
              | uu____6160 -> tm))
let reduce_equality:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___158_6167 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___158_6167.tcenv);
           delta_level = (uu___158_6167.delta_level);
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
        let uu___159_6199 = t in
        {
          FStar_Syntax_Syntax.n = (uu___159_6199.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___159_6199.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___159_6199.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid ->
            FStar_Pervasives_Native.Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid ->
            FStar_Pervasives_Native.Some false
        | uu____6222 -> FStar_Pervasives_Native.None in
      let simplify arg = ((simp_t (FStar_Pervasives_Native.fst arg)), arg) in
      let uu____6271 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps) in
      if uu____6271
      then reduce_primops cfg tm
      else
        (match tm.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.tk = uu____6274;
                     FStar_Syntax_Syntax.pos = uu____6275;
                     FStar_Syntax_Syntax.vars = uu____6276;_},uu____6277);
                FStar_Syntax_Syntax.tk = uu____6278;
                FStar_Syntax_Syntax.pos = uu____6279;
                FStar_Syntax_Syntax.vars = uu____6280;_},args)
             ->
             let uu____6318 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
             if uu____6318
             then
               let uu____6319 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____6319 with
                | (FStar_Pervasives_Native.Some (true ),uu____6384)::
                    (uu____6385,(arg,uu____6387))::[] -> arg
                | (uu____6468,(arg,uu____6470))::(FStar_Pervasives_Native.Some
                                                  (true ),uu____6471)::[]
                    -> arg
                | (FStar_Pervasives_Native.Some (false ),uu____6552)::uu____6553::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____6628::(FStar_Pervasives_Native.Some (false
                               ),uu____6629)::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____6704 -> tm)
             else
               (let uu____6722 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
                if uu____6722
                then
                  let uu____6723 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____6723 with
                  | (FStar_Pervasives_Native.Some (true ),uu____6788)::uu____6789::[]
                      -> w FStar_Syntax_Util.t_true
                  | uu____6864::(FStar_Pervasives_Native.Some (true
                                 ),uu____6865)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____6940)::
                      (uu____6941,(arg,uu____6943))::[] -> arg
                  | (uu____7024,(arg,uu____7026))::(FStar_Pervasives_Native.Some
                                                    (false ),uu____7027)::[]
                      -> arg
                  | uu____7108 -> tm
                else
                  (let uu____7126 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.imp_lid in
                   if uu____7126
                   then
                     let uu____7127 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____7127 with
                     | uu____7192::(FStar_Pervasives_Native.Some (true
                                    ),uu____7193)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____7268)::uu____7269::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____7344)::
                         (uu____7345,(arg,uu____7347))::[] -> arg
                     | uu____7428 -> tm
                   else
                     (let uu____7446 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____7446
                      then
                        let uu____7447 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____7447 with
                        | (FStar_Pervasives_Native.Some (true ),uu____7512)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____7559)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____7606 -> tm
                      else
                        (let uu____7624 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____7624
                         then
                           match args with
                           | (t,uu____7626)::[] ->
                               let uu____7651 =
                                 let uu____7652 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____7652.FStar_Syntax_Syntax.n in
                               (match uu____7651 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____7657::[],body,uu____7659) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____7710 -> tm)
                                | uu____7713 -> tm)
                           | (uu____7714,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____7715))::
                               (t,uu____7717)::[] ->
                               let uu____7770 =
                                 let uu____7771 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____7771.FStar_Syntax_Syntax.n in
                               (match uu____7770 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____7776::[],body,uu____7778) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____7829 -> tm)
                                | uu____7832 -> tm)
                           | uu____7833 -> tm
                         else
                           (let uu____7845 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____7845
                            then
                              match args with
                              | (t,uu____7847)::[] ->
                                  let uu____7872 =
                                    let uu____7873 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____7873.FStar_Syntax_Syntax.n in
                                  (match uu____7872 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____7878::[],body,uu____7880) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____7931 -> tm)
                                   | uu____7934 -> tm)
                              | (uu____7935,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____7936))::
                                  (t,uu____7938)::[] ->
                                  let uu____7991 =
                                    let uu____7992 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____7992.FStar_Syntax_Syntax.n in
                                  (match uu____7991 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____7997::[],body,uu____7999) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____8050 -> tm)
                                   | uu____8053 -> tm)
                              | uu____8054 -> tm
                            else reduce_equality cfg tm)))))
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                FStar_Syntax_Syntax.tk = uu____8067;
                FStar_Syntax_Syntax.pos = uu____8068;
                FStar_Syntax_Syntax.vars = uu____8069;_},args)
             ->
             let uu____8099 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
             if uu____8099
             then
               let uu____8100 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____8100 with
                | (FStar_Pervasives_Native.Some (true ),uu____8165)::
                    (uu____8166,(arg,uu____8168))::[] -> arg
                | (uu____8249,(arg,uu____8251))::(FStar_Pervasives_Native.Some
                                                  (true ),uu____8252)::[]
                    -> arg
                | (FStar_Pervasives_Native.Some (false ),uu____8333)::uu____8334::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____8409::(FStar_Pervasives_Native.Some (false
                               ),uu____8410)::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____8485 -> tm)
             else
               (let uu____8503 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
                if uu____8503
                then
                  let uu____8504 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____8504 with
                  | (FStar_Pervasives_Native.Some (true ),uu____8569)::uu____8570::[]
                      -> w FStar_Syntax_Util.t_true
                  | uu____8645::(FStar_Pervasives_Native.Some (true
                                 ),uu____8646)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____8721)::
                      (uu____8722,(arg,uu____8724))::[] -> arg
                  | (uu____8805,(arg,uu____8807))::(FStar_Pervasives_Native.Some
                                                    (false ),uu____8808)::[]
                      -> arg
                  | uu____8889 -> tm
                else
                  (let uu____8907 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.imp_lid in
                   if uu____8907
                   then
                     let uu____8908 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____8908 with
                     | uu____8973::(FStar_Pervasives_Native.Some (true
                                    ),uu____8974)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____9049)::uu____9050::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____9125)::
                         (uu____9126,(arg,uu____9128))::[] -> arg
                     | uu____9209 -> tm
                   else
                     (let uu____9227 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____9227
                      then
                        let uu____9228 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____9228 with
                        | (FStar_Pervasives_Native.Some (true ),uu____9293)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____9340)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____9387 -> tm
                      else
                        (let uu____9405 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____9405
                         then
                           match args with
                           | (t,uu____9407)::[] ->
                               let uu____9432 =
                                 let uu____9433 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____9433.FStar_Syntax_Syntax.n in
                               (match uu____9432 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____9438::[],body,uu____9440) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____9491 -> tm)
                                | uu____9494 -> tm)
                           | (uu____9495,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____9496))::
                               (t,uu____9498)::[] ->
                               let uu____9551 =
                                 let uu____9552 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____9552.FStar_Syntax_Syntax.n in
                               (match uu____9551 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____9557::[],body,uu____9559) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____9610 -> tm)
                                | uu____9613 -> tm)
                           | uu____9614 -> tm
                         else
                           (let uu____9626 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____9626
                            then
                              match args with
                              | (t,uu____9628)::[] ->
                                  let uu____9653 =
                                    let uu____9654 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____9654.FStar_Syntax_Syntax.n in
                                  (match uu____9653 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____9659::[],body,uu____9661) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____9712 -> tm)
                                   | uu____9715 -> tm)
                              | (uu____9716,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____9717))::
                                  (t,uu____9719)::[] ->
                                  let uu____9772 =
                                    let uu____9773 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____9773.FStar_Syntax_Syntax.n in
                                  (match uu____9772 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____9778::[],body,uu____9780) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____9831 -> tm)
                                   | uu____9834 -> tm)
                              | uu____9835 -> tm
                            else reduce_equality cfg tm)))))
         | uu____9847 -> tm)
let is_norm_request hd1 args =
  let uu____9864 =
    let uu____9871 =
      let uu____9872 = FStar_Syntax_Util.un_uinst hd1 in
      uu____9872.FStar_Syntax_Syntax.n in
    (uu____9871, args) in
  match uu____9864 with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____9880::uu____9881::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____9885::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
  | uu____9888 -> false
let get_norm_request args =
  match args with
  | uu____9916::(tm,uu____9918)::[] -> tm
  | (tm,uu____9936)::[] -> tm
  | uu____9945 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___135_9956  ->
    match uu___135_9956 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.tk = uu____9959;
           FStar_Syntax_Syntax.pos = uu____9960;
           FStar_Syntax_Syntax.vars = uu____9961;_},uu____9962,uu____9963))::uu____9964
        -> true
    | uu____9975 -> false
let is_fstar_tactics_embed: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____9981 =
      let uu____9982 = FStar_Syntax_Util.un_uinst t in
      uu____9982.FStar_Syntax_Syntax.n in
    match uu____9981 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Parser_Const.fstar_tactics_embed_lid
    | uu____9988 -> false
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
            (fun uu____10133  ->
               let uu____10134 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____10135 = FStar_Syntax_Print.term_to_string t1 in
               let uu____10136 =
                 let uu____10137 =
                   let uu____10140 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____10140 in
                 stack_to_string uu____10137 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____10134
                 uu____10135 uu____10136);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____10163 ->
               failwith "Impossible"
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____10202 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____10219 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____10220 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10221;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____10222;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10231;
                 FStar_Syntax_Syntax.fv_delta = uu____10232;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10239;
                 FStar_Syntax_Syntax.fv_delta = uu____10240;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____10241);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.tk = uu____10255;
                  FStar_Syntax_Syntax.pos = uu____10256;
                  FStar_Syntax_Syntax.vars = uu____10257;_},uu____10258)
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.fstar_tactics_embed_lid
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               is_fstar_tactics_embed hd1 ->
               let args1 = closures_as_args_delayed cfg env args in
               let t2 =
                 let uu___160_10333 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd1, args1));
                   FStar_Syntax_Syntax.tk =
                     (uu___160_10333.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___160_10333.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___160_10333.FStar_Syntax_Syntax.vars)
                 } in
               let t3 = reduce_primops cfg t2 in rebuild cfg env stack1 t3
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____10379 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____10379) && (is_norm_request hd1 args))
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
                 let uu___161_10401 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___161_10401.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___161_10401.primitive_steps)
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
                  FStar_Syntax_Syntax.tk = uu____10409;
                  FStar_Syntax_Syntax.pos = uu____10410;
                  FStar_Syntax_Syntax.vars = uu____10411;_},a1::a2::rest)
               ->
               let uu____10475 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____10475 with
                | (hd1,uu____10495) ->
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
                    (FStar_Const.Const_reflect uu____10586);
                  FStar_Syntax_Syntax.tk = uu____10587;
                  FStar_Syntax_Syntax.pos = uu____10588;
                  FStar_Syntax_Syntax.vars = uu____10589;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____10633 = FStar_List.tl stack1 in
               norm cfg env uu____10633 (FStar_Pervasives_Native.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.tk = uu____10638;
                  FStar_Syntax_Syntax.pos = uu____10639;
                  FStar_Syntax_Syntax.vars = uu____10640;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____10684 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____10684 with
                | (reify_head,uu____10704) ->
                    let a1 =
                      let uu____10734 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (FStar_Pervasives_Native.fst a) in
                      FStar_Syntax_Subst.compress uu____10734 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____10739);
                            FStar_Syntax_Syntax.tk = uu____10740;
                            FStar_Syntax_Syntax.pos = uu____10741;
                            FStar_Syntax_Syntax.vars = uu____10742;_},a2::[])
                         ->
                         norm cfg env stack1 (FStar_Pervasives_Native.fst a2)
                     | uu____10790 ->
                         let stack2 =
                           (App
                              (reify_head, FStar_Pervasives_Native.None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____10802 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____10802
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____10813 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____10813
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____10816 =
                      let uu____10823 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____10823, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____10816 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___136_10836  ->
                         match uu___136_10836 with
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
                    let uu____10840 = FStar_Syntax_Syntax.range_of_fv f in
                    FStar_TypeChecker_Env.set_range cfg.tcenv uu____10840 in
                  let uu____10841 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  match uu____10841 with
                  | FStar_Pervasives_Native.None  ->
                      (log cfg
                         (fun uu____10857  ->
                            FStar_Util.print "Tm_fvar case 2\n" []);
                       rebuild cfg env stack1 t1)
                  | FStar_Pervasives_Native.Some (us,t2) ->
                      (log cfg
                         (fun uu____10865  ->
                            let uu____10866 =
                              FStar_Syntax_Print.term_to_string t0 in
                            let uu____10867 =
                              FStar_Syntax_Print.term_to_string t2 in
                            FStar_Util.print2 ">>> Unfolded %s to %s\n"
                              uu____10866 uu____10867);
                       (let t3 =
                          let uu____10869 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 (UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant)) in
                          if uu____10869
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
                          | (UnivArgs (us',uu____10880))::stack2 ->
                              let env1 =
                                FStar_All.pipe_right us'
                                  (FStar_List.fold_left
                                     (fun env1  -> fun u  -> (Univ u) :: env1)
                                     env) in
                              norm cfg env1 stack2 t3
                          | uu____10901 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack1 t3
                          | uu____10902 ->
                              let uu____10903 =
                                let uu____10904 =
                                  FStar_Syntax_Print.lid_to_string
                                    (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                FStar_Util.format1
                                  "Impossible: missing universe instantiation on %s"
                                  uu____10904 in
                              failwith uu____10903
                        else norm cfg env stack1 t3)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____10911 = lookup_bvar env x in
               (match uu____10911 with
                | Univ uu____10912 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____10937 = FStar_ST.read r in
                      (match uu____10937 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____10969  ->
                                 let uu____10970 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____10971 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____10970
                                   uu____10971);
                            (let uu____10972 =
                               let uu____10973 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____10973.FStar_Syntax_Syntax.n in
                             match uu____10972 with
                             | FStar_Syntax_Syntax.Tm_abs uu____10978 ->
                                 norm cfg env2 stack1 t'
                             | uu____11007 -> rebuild cfg env2 stack1 t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____11065)::uu____11066 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11075)::uu____11076 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11086,uu____11087))::stack_rest ->
                    (match c with
                     | Univ uu____11091 -> norm cfg (c :: env) stack_rest t1
                     | uu____11092 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____11097::[] ->
                              (match lopt with
                               | FStar_Pervasives_Native.None  when
                                   FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____11121  ->
                                         let uu____11122 =
                                           closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____11122);
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
                                           (fun uu___137_11147  ->
                                              match uu___137_11147 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____11148 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____11150  ->
                                         let uu____11151 =
                                           closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____11151);
                                    norm cfg (c :: env) stack_rest body)
                               | FStar_Pervasives_Native.Some (FStar_Util.Inl
                                   lc) when
                                   FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                                   ->
                                   (log cfg
                                      (fun uu____11170  ->
                                         let uu____11171 =
                                           closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____11171);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____11172 when
                                   FStar_All.pipe_right cfg.steps
                                     (FStar_List.contains Reify)
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____11185 ->
                                   let cfg1 =
                                     let uu___162_11199 = cfg in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___162_11199.tcenv);
                                       delta_level =
                                         (uu___162_11199.delta_level);
                                       primitive_steps =
                                         (uu___162_11199.primitive_steps)
                                     } in
                                   let uu____11200 =
                                     closure_as_term cfg1 env t1 in
                                   rebuild cfg1 env stack1 uu____11200)
                          | uu____11201::tl1 ->
                              (log cfg
                                 (fun uu____11218  ->
                                    let uu____11219 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11219);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___163_11261 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___163_11261.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____11280  ->
                          let uu____11281 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11281);
                     norm cfg env stack2 t1)
                | (Debug uu____11282)::uu____11283 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11286 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11286
                    else
                      (let uu____11288 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11288 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some (FStar_Util.Inl
                                 l) ->
                                 let uu____11340 =
                                   let uu____11351 =
                                     let uu____11352 =
                                       let uu____11353 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____11353 in
                                     FStar_All.pipe_right uu____11352
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____11351
                                     (fun _0_31  -> FStar_Util.Inl _0_31) in
                                 FStar_All.pipe_right uu____11340
                                   (fun _0_32  ->
                                      FStar_Pervasives_Native.Some _0_32)
                             | uu____11402 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11427  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____11435  ->
                                 let uu____11436 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11436);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___164_11449 = cfg in
                               let uu____11450 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___164_11449.steps);
                                 tcenv = (uu___164_11449.tcenv);
                                 delta_level = (uu___164_11449.delta_level);
                                 primitive_steps = uu____11450
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____11468)::uu____11469 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11476 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11476
                    else
                      (let uu____11478 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11478 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some (FStar_Util.Inl
                                 l) ->
                                 let uu____11530 =
                                   let uu____11541 =
                                     let uu____11542 =
                                       let uu____11543 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____11543 in
                                     FStar_All.pipe_right uu____11542
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____11541
                                     (fun _0_33  -> FStar_Util.Inl _0_33) in
                                 FStar_All.pipe_right uu____11530
                                   (fun _0_34  ->
                                      FStar_Pervasives_Native.Some _0_34)
                             | uu____11592 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11617  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____11625  ->
                                 let uu____11626 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11626);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___164_11639 = cfg in
                               let uu____11640 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___164_11639.steps);
                                 tcenv = (uu___164_11639.tcenv);
                                 delta_level = (uu___164_11639.delta_level);
                                 primitive_steps = uu____11640
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____11658)::uu____11659 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11670 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11670
                    else
                      (let uu____11672 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11672 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some (FStar_Util.Inl
                                 l) ->
                                 let uu____11724 =
                                   let uu____11735 =
                                     let uu____11736 =
                                       let uu____11737 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____11737 in
                                     FStar_All.pipe_right uu____11736
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____11735
                                     (fun _0_35  -> FStar_Util.Inl _0_35) in
                                 FStar_All.pipe_right uu____11724
                                   (fun _0_36  ->
                                      FStar_Pervasives_Native.Some _0_36)
                             | uu____11786 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11811  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____11819  ->
                                 let uu____11820 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11820);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___164_11833 = cfg in
                               let uu____11834 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___164_11833.steps);
                                 tcenv = (uu___164_11833.tcenv);
                                 delta_level = (uu___164_11833.delta_level);
                                 primitive_steps = uu____11834
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____11852)::uu____11853 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11862 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11862
                    else
                      (let uu____11864 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11864 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some (FStar_Util.Inl
                                 l) ->
                                 let uu____11916 =
                                   let uu____11927 =
                                     let uu____11928 =
                                       let uu____11929 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____11929 in
                                     FStar_All.pipe_right uu____11928
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____11927
                                     (fun _0_37  -> FStar_Util.Inl _0_37) in
                                 FStar_All.pipe_right uu____11916
                                   (fun _0_38  ->
                                      FStar_Pervasives_Native.Some _0_38)
                             | uu____11978 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12003  -> Dummy :: env1) env) in
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
                             let cfg1 =
                               let uu___164_12025 = cfg in
                               let uu____12026 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___164_12025.steps);
                                 tcenv = (uu___164_12025.tcenv);
                                 delta_level = (uu___164_12025.delta_level);
                                 primitive_steps = uu____12026
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____12044)::uu____12045 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12064 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12064
                    else
                      (let uu____12066 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12066 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some (FStar_Util.Inl
                                 l) ->
                                 let uu____12118 =
                                   let uu____12129 =
                                     let uu____12130 =
                                       let uu____12131 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____12131 in
                                     FStar_All.pipe_right uu____12130
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____12129
                                     (fun _0_39  -> FStar_Util.Inl _0_39) in
                                 FStar_All.pipe_right uu____12118
                                   (fun _0_40  ->
                                      FStar_Pervasives_Native.Some _0_40)
                             | uu____12180 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12205  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____12213  ->
                                 let uu____12214 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12214);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___164_12227 = cfg in
                               let uu____12228 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___164_12227.steps);
                                 tcenv = (uu___164_12227.tcenv);
                                 delta_level = (uu___164_12227.delta_level);
                                 primitive_steps = uu____12228
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12246 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12246
                    else
                      (let uu____12248 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12248 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some (FStar_Util.Inl
                                 l) ->
                                 let uu____12300 =
                                   let uu____12311 =
                                     let uu____12312 =
                                       let uu____12313 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____12313 in
                                     FStar_All.pipe_right uu____12312
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____12311
                                     (fun _0_41  -> FStar_Util.Inl _0_41) in
                                 FStar_All.pipe_right uu____12300
                                   (fun _0_42  ->
                                      FStar_Pervasives_Native.Some _0_42)
                             | uu____12362 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12387  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____12395  ->
                                 let uu____12396 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12396);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___164_12409 = cfg in
                               let uu____12410 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___164_12409.steps);
                                 tcenv = (uu___164_12409.tcenv);
                                 delta_level = (uu___164_12409.delta_level);
                                 primitive_steps = uu____12410
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
                      (fun uu____12469  ->
                         fun stack2  ->
                           match uu____12469 with
                           | (a,aq) ->
                               let uu____12481 =
                                 let uu____12482 =
                                   let uu____12489 =
                                     let uu____12490 =
                                       let uu____12509 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____12509, false) in
                                     Clos uu____12490 in
                                   (uu____12489, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____12482 in
                               uu____12481 :: stack2) args) in
               (log cfg
                  (fun uu____12547  ->
                     let uu____12548 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12548);
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
                             ((let uu___165_12581 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___165_12581.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___165_12581.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____12582 ->
                      let uu____12587 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12587)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____12590 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____12590 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____12617 =
                          let uu____12618 =
                            let uu____12627 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___166_12628 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___166_12628.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___166_12628.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12627) in
                          FStar_Syntax_Syntax.Tm_refine uu____12618 in
                        mk uu____12617 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____12651 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____12651
               else
                 (let uu____12653 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____12653 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12661 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12671  -> Dummy :: env1) env) in
                        norm_comp cfg uu____12661 c1 in
                      let t2 =
                        let uu____12683 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____12683 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____12764)::uu____12765 -> norm cfg env stack1 t11
                | (Arg uu____12774)::uu____12775 -> norm cfg env stack1 t11
                | (App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.tk = uu____12784;
                       FStar_Syntax_Syntax.pos = uu____12785;
                       FStar_Syntax_Syntax.vars = uu____12786;_},uu____12787,uu____12788))::uu____12789
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____12800)::uu____12801 ->
                    norm cfg env stack1 t11
                | uu____12810 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____12813  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____12836 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____12836
                        | FStar_Util.Inr c ->
                            let uu____12850 = norm_comp cfg env c in
                            FStar_Util.Inr uu____12850 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____12858 =
                        mk
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (t12, (tc1, tacopt1), l))
                          t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____12858)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____12956,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____12957;
                               FStar_Syntax_Syntax.lbunivs = uu____12958;
                               FStar_Syntax_Syntax.lbtyp = uu____12959;
                               FStar_Syntax_Syntax.lbeff = uu____12960;
                               FStar_Syntax_Syntax.lbdef = uu____12961;_}::uu____12962),uu____12963)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____13011 =
                 (let uu____13012 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____13012) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____13013 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____13013))) in
               if uu____13011
               then
                 let env1 =
                   let uu____13017 =
                     let uu____13018 =
                       let uu____13037 =
                         FStar_Util.mk_ref FStar_Pervasives_Native.None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____13037,
                         false) in
                     Clos uu____13018 in
                   uu____13017 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____13079 =
                    let uu____13084 =
                      let uu____13085 =
                        let uu____13086 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____13086
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____13085] in
                    FStar_Syntax_Subst.open_term uu____13084 body in
                  match uu____13079 with
                  | (bs,body1) ->
                      let lb1 =
                        let uu___167_13094 = lb in
                        let uu____13095 =
                          let uu____13100 =
                            let uu____13101 = FStar_List.hd bs in
                            FStar_All.pipe_right uu____13101
                              FStar_Pervasives_Native.fst in
                          FStar_All.pipe_right uu____13100
                            (fun _0_43  -> FStar_Util.Inl _0_43) in
                        let uu____13118 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____13123 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = uu____13095;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___167_13094.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____13118;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___167_13094.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____13123
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____13140  -> Dummy :: env1)
                             env) in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____13169 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____13169
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13192 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13234  ->
                        match uu____13234 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____13307 =
                                let uu___168_13308 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___168_13308.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___168_13308.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____13307 in
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
               (match uu____13192 with
                | (rec_env,memos,uu____13416) ->
                    let uu____13445 =
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
                             let uu____13520 =
                               let uu____13521 =
                                 let uu____13540 =
                                   FStar_Util.mk_ref
                                     FStar_Pervasives_Native.None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____13540, false) in
                               Clos uu____13521 in
                             uu____13520 :: env1)
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
                             FStar_Syntax_Syntax.tk = uu____13606;
                             FStar_Syntax_Syntax.pos = uu____13607;
                             FStar_Syntax_Syntax.vars = uu____13608;_},uu____13609,uu____13610))::uu____13611
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____13622 -> false in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____13632 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____13632
                        then
                          let uu___169_13633 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___169_13633.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps =
                              (uu___169_13633.primitive_steps)
                          }
                        else
                          (let uu___170_13635 = cfg in
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___170_13635.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta];
                             primitive_steps =
                               (uu___170_13635.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____13637 =
                         let uu____13638 = FStar_Syntax_Subst.compress head1 in
                         uu____13638.FStar_Syntax_Syntax.n in
                       match uu____13637 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____13662 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____13662 with
                            | (uu____13663,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____13669 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____13677 =
                                         let uu____13678 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____13678.FStar_Syntax_Syntax.n in
                                       match uu____13677 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____13686,uu____13687))
                                           ->
                                           let uu____13704 =
                                             let uu____13705 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____13705.FStar_Syntax_Syntax.n in
                                           (match uu____13704 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____13713,msrc,uu____13715))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____13732 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____13732
                                            | uu____13733 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____13734 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____13735 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____13735 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___171_13740 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___171_13740.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___171_13740.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___171_13740.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____13741 =
                                            FStar_List.tl stack1 in
                                          let uu____13742 =
                                            let uu____13743 =
                                              let uu____13748 =
                                                let uu____13749 =
                                                  let uu____13764 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____13764) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____13749 in
                                              FStar_Syntax_Syntax.mk
                                                uu____13748 in
                                            uu____13743
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____13741
                                            uu____13742
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____13785 =
                                            let uu____13786 = is_return body in
                                            match uu____13786 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____13790;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____13791;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____13792;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____13801 -> false in
                                          if uu____13785
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
                                               let uu____13836 =
                                                 let uu____13841 =
                                                   let uu____13842 =
                                                     let uu____13871 =
                                                       let uu____13874 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____13874] in
                                                     (uu____13871, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          (FStar_Util.Inr
                                                             (m1, [])))) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____13842 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____13841 in
                                               uu____13836
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____13923 =
                                                 let uu____13924 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____13924.FStar_Syntax_Syntax.n in
                                               match uu____13923 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____13934::uu____13935::[])
                                                   ->
                                                   let uu____13946 =
                                                     let uu____13951 =
                                                       let uu____13952 =
                                                         let uu____13961 =
                                                           let uu____13964 =
                                                             let uu____13965
                                                               =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____13965 in
                                                           let uu____13966 =
                                                             let uu____13969
                                                               =
                                                               let uu____13970
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____13970 in
                                                             [uu____13969] in
                                                           uu____13964 ::
                                                             uu____13966 in
                                                         (bind1, uu____13961) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____13952 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____13951 in
                                                   uu____13946
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____13981 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____13991 =
                                                 let uu____13996 =
                                                   let uu____13997 =
                                                     let uu____14016 =
                                                       let uu____14019 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____14020 =
                                                         let uu____14023 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____14024 =
                                                           let uu____14027 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____14028 =
                                                             let uu____14031
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____14032
                                                               =
                                                               let uu____14035
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____14036
                                                                 =
                                                                 let uu____14039
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____14039] in
                                                               uu____14035 ::
                                                                 uu____14036 in
                                                             uu____14031 ::
                                                               uu____14032 in
                                                           uu____14027 ::
                                                             uu____14028 in
                                                         uu____14023 ::
                                                           uu____14024 in
                                                       uu____14019 ::
                                                         uu____14020 in
                                                     (bind_inst, uu____14016) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____13997 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____13996 in
                                               uu____13991
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____14050 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____14050 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____14082 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____14082 with
                            | (uu____14083,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____14118 =
                                        let uu____14119 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____14119.FStar_Syntax_Syntax.n in
                                      match uu____14118 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____14129) -> t4
                                      | uu____14138 -> head2 in
                                    let uu____14139 =
                                      let uu____14140 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____14140.FStar_Syntax_Syntax.n in
                                    match uu____14139 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____14148 ->
                                        FStar_Pervasives_Native.None in
                                  let uu____14149 = maybe_extract_fv head2 in
                                  match uu____14149 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____14159 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____14159
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____14164 =
                                          maybe_extract_fv head3 in
                                        match uu____14164 with
                                        | FStar_Pervasives_Native.Some
                                            uu____14169 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____14170 ->
                                            FStar_Pervasives_Native.Some
                                              false in
                                      (head3, action_unfolded)
                                  | uu____14175 ->
                                      (head2, FStar_Pervasives_Native.None) in
                                ((let is_arg_impure uu____14192 =
                                    match uu____14192 with
                                    | (e,q) ->
                                        let uu____14199 =
                                          let uu____14200 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____14200.FStar_Syntax_Syntax.n in
                                        (match uu____14199 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____14225 -> false) in
                                  let uu____14226 =
                                    let uu____14227 =
                                      let uu____14234 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____14234 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____14227 in
                                  if uu____14226
                                  then
                                    let uu____14239 =
                                      let uu____14240 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____14240 in
                                    failwith uu____14239
                                  else ());
                                 (let uu____14242 =
                                    maybe_unfold_action head_app in
                                  match uu____14242 with
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
                                      let uu____14295 = FStar_List.tl stack1 in
                                      norm cfg env uu____14295 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____14317 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____14317 in
                           let uu____14318 = FStar_List.tl stack1 in
                           norm cfg env uu____14318 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____14480  ->
                                     match uu____14480 with
                                     | (pat,wopt,tm) ->
                                         let uu____14552 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____14552))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____14602 = FStar_List.tl stack1 in
                           norm cfg env uu____14602 tm
                       | uu____14603 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.tk = uu____14616;
                             FStar_Syntax_Syntax.pos = uu____14617;
                             FStar_Syntax_Syntax.vars = uu____14618;_},uu____14619,uu____14620))::uu____14621
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____14632 -> false in
                    if should_reify
                    then
                      let uu____14633 = FStar_List.tl stack1 in
                      let uu____14634 =
                        let uu____14635 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____14635 in
                      norm cfg env uu____14633 uu____14634
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____14638 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____14638
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___172_14647 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___172_14647.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___172_14647.primitive_steps)
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
                | uu____14649 ->
                    (match stack1 with
                     | uu____14650::uu____14651 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled
                              (l,r,uu____14656) ->
                              norm cfg env ((Meta (m, r)) :: stack1) head1
                          | FStar_Syntax_Syntax.Meta_pattern args ->
                              let args1 = norm_pattern_args cfg env args in
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_pattern args1),
                                      (t1.FStar_Syntax_Syntax.pos))) ::
                                stack1) head1
                          | uu____14683 -> norm cfg env stack1 head1)
                     | [] ->
                         let head2 = norm cfg env [] head1 in
                         let m1 =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               let uu____14699 =
                                 norm_pattern_args cfg env args in
                               FStar_Syntax_Syntax.Meta_pattern uu____14699
                           | uu____14712 -> m in
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
              let uu____14728 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____14728 with
              | (uu____14729,return_repr) ->
                  let return_inst =
                    let uu____14740 =
                      let uu____14741 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____14741.FStar_Syntax_Syntax.n in
                    match uu____14740 with
                    | FStar_Syntax_Syntax.Tm_uinst
                        (return_tm,uu____14751::[]) ->
                        let uu____14762 =
                          let uu____14767 =
                            let uu____14768 =
                              let uu____14777 =
                                let uu____14780 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____14780] in
                              (return_tm, uu____14777) in
                            FStar_Syntax_Syntax.Tm_uinst uu____14768 in
                          FStar_Syntax_Syntax.mk uu____14767 in
                        uu____14762 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____14791 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____14796 =
                    let uu____14801 =
                      let uu____14802 =
                        let uu____14821 =
                          let uu____14824 = FStar_Syntax_Syntax.as_arg t in
                          let uu____14825 =
                            let uu____14828 = FStar_Syntax_Syntax.as_arg e in
                            [uu____14828] in
                          uu____14824 :: uu____14825 in
                        (return_inst, uu____14821) in
                      FStar_Syntax_Syntax.Tm_app uu____14802 in
                    FStar_Syntax_Syntax.mk uu____14801 in
                  uu____14796 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____14840 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____14840 with
               | FStar_Pervasives_Native.None  ->
                   let uu____14843 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____14843
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____14844;
                     FStar_TypeChecker_Env.mtarget = uu____14845;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____14846;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____14857;
                     FStar_TypeChecker_Env.mtarget = uu____14858;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____14859;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____14877 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____14877)
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
                (fun uu____14933  ->
                   match uu____14933 with
                   | (a,imp) ->
                       let uu____14944 = norm cfg env [] a in
                       (uu____14944, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___173_14967 = comp1 in
            let uu____14972 =
              let uu____14973 =
                let uu____14984 = norm cfg env [] t in
                let uu____14985 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____14984, uu____14985) in
              FStar_Syntax_Syntax.Total uu____14973 in
            {
              FStar_Syntax_Syntax.n = uu____14972;
              FStar_Syntax_Syntax.tk =
                (uu___173_14967.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___173_14967.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___173_14967.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___174_15004 = comp1 in
            let uu____15009 =
              let uu____15010 =
                let uu____15021 = norm cfg env [] t in
                let uu____15022 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____15021, uu____15022) in
              FStar_Syntax_Syntax.GTotal uu____15010 in
            {
              FStar_Syntax_Syntax.n = uu____15009;
              FStar_Syntax_Syntax.tk =
                (uu___174_15004.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___174_15004.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___174_15004.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____15070  ->
                      match uu____15070 with
                      | (a,i) ->
                          let uu____15081 = norm cfg env [] a in
                          (uu____15081, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___138_15089  ->
                      match uu___138_15089 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____15095 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____15095
                      | f -> f)) in
            let uu___175_15101 = comp1 in
            let uu____15106 =
              let uu____15107 =
                let uu___176_15108 = ct in
                let uu____15109 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____15110 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____15115 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____15109;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___176_15108.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____15110;
                  FStar_Syntax_Syntax.effect_args = uu____15115;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____15107 in
            {
              FStar_Syntax_Syntax.n = uu____15106;
              FStar_Syntax_Syntax.tk =
                (uu___175_15101.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___175_15101.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___175_15101.FStar_Syntax_Syntax.vars)
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
            (let uu___177_15133 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___177_15133.tcenv);
               delta_level = (uu___177_15133.delta_level);
               primitive_steps = (uu___177_15133.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____15138 = norm1 t in
          FStar_Syntax_Util.non_informative uu____15138 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____15143 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___178_15168 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.tk =
                (uu___178_15168.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___178_15168.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___178_15168.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____15177 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____15177
            then
              let ct1 =
                match downgrade_ghost_effect_name
                        ct.FStar_Syntax_Syntax.effect_name
                with
                | FStar_Pervasives_Native.Some pure_eff ->
                    let uu___179_15184 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___179_15184.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___179_15184.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___179_15184.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___179_15184.FStar_Syntax_Syntax.flags)
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___180_15186 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___180_15186.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___180_15186.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___180_15186.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___180_15186.FStar_Syntax_Syntax.flags)
                    } in
              let uu___181_15187 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.tk =
                  (uu___181_15187.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___181_15187.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___181_15187.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____15189 -> c
and norm_binder:
  cfg ->
    env ->
      FStar_Syntax_Syntax.binder ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
          FStar_Pervasives_Native.tuple2
  =
  fun cfg  ->
    fun env  ->
      fun uu____15192  ->
        match uu____15192 with
        | (x,imp) ->
            let uu____15195 =
              let uu___182_15196 = x in
              let uu____15197 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___182_15196.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___182_15196.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____15197
              } in
            (uu____15195, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____15205 =
          FStar_List.fold_left
            (fun uu____15218  ->
               fun b  ->
                 match uu____15218 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____15205 with | (nbs,uu____15246) -> FStar_List.rev nbs
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
            let uu____15274 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
            if uu____15274
            then
              let t = norm cfg env [] lc.FStar_Syntax_Syntax.res_typ in
              let uu____15282 = FStar_Syntax_Util.is_total_lcomp lc in
              (if uu____15282
               then
                 let uu____15289 =
                   let uu____15294 =
                     let uu____15295 =
                       let uu____15300 = FStar_Syntax_Syntax.mk_Total t in
                       FStar_Syntax_Util.comp_set_flags uu____15300 flags in
                     FStar_Syntax_Util.lcomp_of_comp uu____15295 in
                   FStar_Util.Inl uu____15294 in
                 FStar_Pervasives_Native.Some uu____15289
               else
                 (let uu____15306 =
                    let uu____15311 =
                      let uu____15312 =
                        let uu____15317 = FStar_Syntax_Syntax.mk_GTotal t in
                        FStar_Syntax_Util.comp_set_flags uu____15317 flags in
                      FStar_Syntax_Util.lcomp_of_comp uu____15312 in
                    FStar_Util.Inl uu____15311 in
                  FStar_Pervasives_Native.Some uu____15306))
            else
              FStar_Pervasives_Native.Some
                (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags))
        | uu____15341 -> lopt
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
              ((let uu____15357 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____15357
                then
                  let uu____15358 = FStar_Syntax_Print.term_to_string tm in
                  let uu____15359 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2 "Normalized %s to %s\n" uu____15358
                    uu____15359
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___183_15375 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___183_15375.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____15404  ->
                    let uu____15405 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____15405);
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
              let uu____15455 =
                let uu___184_15456 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___184_15456.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___184_15456.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___184_15456.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____15455
          | (Arg (Univ uu____15457,uu____15458,uu____15459))::uu____15460 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____15463,uu____15464))::uu____15465 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____15481),aq,r))::stack2 ->
              (log cfg
                 (fun uu____15508  ->
                    let uu____15509 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____15509);
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
                 (let uu____15521 = FStar_ST.read m in
                  match uu____15521 with
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
                  | FStar_Pervasives_Native.Some (uu____15559,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq)
                          FStar_Pervasives_Native.None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 =
                FStar_Syntax_Syntax.extend_app head1 (t, aq)
                  FStar_Pervasives_Native.None r in
              let uu____15587 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____15587
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____15595  ->
                    let uu____15596 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____15596);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____15601 =
                  log cfg
                    (fun uu____15603  ->
                       let uu____15604 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____15605 =
                         let uu____15606 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____15619  ->
                                   match uu____15619 with
                                   | (p,uu____15629,uu____15630) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____15606
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____15604 uu____15605);
                  (let whnf = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___139_15646  ->
                               match uu___139_15646 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____15647 -> false)) in
                     let steps' =
                       let uu____15651 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____15651
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___185_15655 = cfg in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___185_15655.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___185_15655.primitive_steps)
                     } in
                   let norm_or_whnf env2 t1 =
                     if whnf
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____15707 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____15736 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____15803  ->
                                   fun uu____15804  ->
                                     match (uu____15803, uu____15804) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____15929 = norm_pat env3 p1 in
                                         (match uu____15929 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____15736 with
                          | (pats1,env3) ->
                              ((let uu___186_16056 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___186_16056.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___186_16056.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___187_16081 = x in
                           let uu____16082 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___187_16081.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___187_16081.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16082
                           } in
                         ((let uu___188_16093 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___188_16093.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___188_16093.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___189_16100 = x in
                           let uu____16101 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___189_16100.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___189_16100.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16101
                           } in
                         ((let uu___190_16112 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___190_16112.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___190_16112.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___191_16128 = x in
                           let uu____16129 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___191_16128.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___191_16128.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16129
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___192_16141 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.ty =
                               (uu___192_16141.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___192_16141.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf -> branches
                     | uu____16147 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____16151 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____16151 with
                                 | (p,wopt,e) ->
                                     let uu____16183 = norm_pat env1 p in
                                     (match uu____16183 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Pervasives_Native.Some w
                                                ->
                                                let uu____16226 =
                                                  norm_or_whnf env2 w in
                                                FStar_Pervasives_Native.Some
                                                  uu____16226 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____16234 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____16234) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____16248) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____16257 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____16258;
                        FStar_Syntax_Syntax.fv_delta = uu____16259;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Data_ctor );_}
                      -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____16266;
                        FStar_Syntax_Syntax.fv_delta = uu____16267;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Record_ctor uu____16268);_}
                      -> true
                  | uu____16281 -> false in
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
                  let uu____16450 =
                    FStar_Syntax_Util.head_and_args scrutinee2 in
                  match uu____16450 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var uu____16511 ->
                           FStar_Util.Inl [scrutinee2]
                       | FStar_Syntax_Syntax.Pat_wild uu____16514 ->
                           FStar_Util.Inl [scrutinee2]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____16517 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____16538 ->
                                let uu____16539 =
                                  let uu____16540 = is_cons head1 in
                                  Prims.op_Negation uu____16540 in
                                FStar_Util.Inr uu____16539)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____16565 =
                             let uu____16566 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____16566.FStar_Syntax_Syntax.n in
                           (match uu____16565 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____16578 ->
                                let uu____16579 =
                                  let uu____16580 = is_cons head1 in
                                  Prims.op_Negation uu____16580 in
                                FStar_Util.Inr uu____16579))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____16643)::rest_a,(p1,uu____16646)::rest_p) ->
                      let uu____16700 = matches_pat t1 p1 in
                      (match uu____16700 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____16725 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____16855 = matches_pat scrutinee1 p1 in
                      (match uu____16855 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____16872  ->
                                 let uu____16873 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____16874 =
                                   let uu____16875 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____16875
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____16873 uu____16874);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____16889 =
                                        let uu____16890 =
                                          let uu____16909 =
                                            FStar_Util.mk_ref
                                              (FStar_Pervasives_Native.Some
                                                 ([], t1)) in
                                          ([], t1, uu____16909, false) in
                                        Clos uu____16890 in
                                      uu____16889 :: env2) env1 s in
                             let uu____16950 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____16950))) in
                let uu____16951 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____16951
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___140_16970  ->
                match uu___140_16970 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | uu____16974 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____16980 -> d in
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
            let uu___193_17005 = config s e in
            {
              steps = (uu___193_17005.steps);
              tcenv = (uu___193_17005.tcenv);
              delta_level = (uu___193_17005.delta_level);
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
      fun t  -> let uu____17024 = config s e in norm_comp uu____17024 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____17031 = config [] env in norm_universe uu____17031 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun c  ->
      let uu____17038 = config [] env in ghost_to_pure_aux uu____17038 [] c
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
        let uu____17050 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____17050 in
      let uu____17051 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____17051
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___194_17053 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___194_17053.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___194_17053.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____17054  ->
                    let uu____17055 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____17055))
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
            ((let uu____17068 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____17068);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____17077 = config [AllowUnboundUniverses] env in
          norm_comp uu____17077 [] c
        with
        | e ->
            ((let uu____17081 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____17081);
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
                   let uu____17134 =
                     let uu____17135 =
                       let uu____17144 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____17144) in
                     FStar_Syntax_Syntax.Tm_refine uu____17135 in
                   mk uu____17134 t01.FStar_Syntax_Syntax.pos
               | uu____17153 -> t2)
          | uu____17154 -> t2 in
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
        let uu____17176 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____17176 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____17205 ->
                 let uu____17212 = FStar_Syntax_Util.abs_formals e in
                 (match uu____17212 with
                  | (actuals,uu____17232,uu____17233) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____17267 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____17267 with
                         | (binders,args) ->
                             let uu____17284 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             let uu____17285 =
                               let uu____17298 =
                                 FStar_All.pipe_right
                                   (FStar_Syntax_Util.lcomp_of_comp c)
                                   (fun _0_44  -> FStar_Util.Inl _0_44) in
                               FStar_All.pipe_right uu____17298
                                 (fun _0_45  ->
                                    FStar_Pervasives_Native.Some _0_45) in
                             FStar_Syntax_Util.abs binders uu____17284
                               uu____17285)))
let eta_expand:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____17363 =
        let uu____17370 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
        (uu____17370, (t.FStar_Syntax_Syntax.n)) in
      match uu____17363 with
      | (FStar_Pervasives_Native.Some sort,uu____17378) ->
          let uu____17381 = mk sort t.FStar_Syntax_Syntax.pos in
          eta_expand_with_type env t uu____17381
      | (uu____17382,FStar_Syntax_Syntax.Tm_name x) ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____17388 ->
          let uu____17395 = FStar_Syntax_Util.head_and_args t in
          (match uu____17395 with
           | (head1,args) ->
               let uu____17444 =
                 let uu____17445 = FStar_Syntax_Subst.compress head1 in
                 uu____17445.FStar_Syntax_Syntax.n in
               (match uu____17444 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____17450,thead) ->
                    let uu____17476 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____17476 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____17526 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___199_17533 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___199_17533.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___199_17533.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___199_17533.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___199_17533.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___199_17533.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___199_17533.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___199_17533.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___199_17533.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___199_17533.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___199_17533.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___199_17533.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___199_17533.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___199_17533.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___199_17533.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___199_17533.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___199_17533.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___199_17533.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___199_17533.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___199_17533.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___199_17533.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___199_17533.FStar_TypeChecker_Env.qname_and_index)
                                 }) t in
                            match uu____17526 with
                            | (uu____17534,ty,uu____17536) ->
                                eta_expand_with_type env t ty))
                | uu____17537 ->
                    let uu____17538 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___200_17545 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___200_17545.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___200_17545.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___200_17545.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___200_17545.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___200_17545.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___200_17545.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___200_17545.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___200_17545.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___200_17545.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___200_17545.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___200_17545.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___200_17545.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___200_17545.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___200_17545.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___200_17545.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___200_17545.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___200_17545.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___200_17545.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___200_17545.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___200_17545.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___200_17545.FStar_TypeChecker_Env.qname_and_index)
                         }) t in
                    (match uu____17538 with
                     | (uu____17546,ty,uu____17548) ->
                         eta_expand_with_type env t ty)))