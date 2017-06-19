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
type steps = step Prims.list
type primitive_step =
  {
  name: FStar_Ident.lid;
  arity: Prims.int;
  strong_reduction_ok: Prims.bool;
  interpretation:
    FStar_Range.range ->
      FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term option;}
type closure =
  | Clos of (closure Prims.list* FStar_Syntax_Syntax.term* (closure
  Prims.list* FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo*
  Prims.bool)
  | Univ of FStar_Syntax_Syntax.universe
  | Dummy
let uu___is_Clos: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Clos _0 -> true | uu____206 -> false
let __proj__Clos__item___0:
  closure ->
    (closure Prims.list* FStar_Syntax_Syntax.term* (closure Prims.list*
      FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo* Prims.bool)
  = fun projectee  -> match projectee with | Clos _0 -> _0
let uu___is_Univ: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____247 -> false
let __proj__Univ__item___0: closure -> FStar_Syntax_Syntax.universe =
  fun projectee  -> match projectee with | Univ _0 -> _0
let uu___is_Dummy: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____260 -> false
type env = closure Prims.list
let closure_to_string: closure -> Prims.string =
  fun uu___135_265  ->
    match uu___135_265 with
    | Clos (uu____266,t,uu____268,uu____269) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____280 -> "Univ"
    | Dummy  -> "dummy"
type cfg =
  {
  steps: steps;
  tcenv: FStar_TypeChecker_Env.env;
  delta_level: FStar_TypeChecker_Env.delta_level Prims.list;
  primitive_steps: primitive_step Prims.list;}
type branches =
  (FStar_Syntax_Syntax.pat* FStar_Syntax_Syntax.term option*
    FStar_Syntax_Syntax.term) Prims.list
type subst_t = FStar_Syntax_Syntax.subst_elt Prims.list
type stack_elt =
  | Arg of (closure* FStar_Syntax_Syntax.aqual* FStar_Range.range)
  | UnivArgs of (FStar_Syntax_Syntax.universe Prims.list* FStar_Range.range)
  | MemoLazy of (env* FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo
  | Match of (env* branches* FStar_Range.range)
  | Abs of (env* FStar_Syntax_Syntax.binders* env*
  (FStar_Syntax_Syntax.lcomp,FStar_Syntax_Syntax.residual_comp)
  FStar_Util.either option* FStar_Range.range)
  | App of (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.aqual*
  FStar_Range.range)
  | Meta of (FStar_Syntax_Syntax.metadata* FStar_Range.range)
  | Let of (env* FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.letbinding*
  FStar_Range.range)
  | Steps of (steps* primitive_step Prims.list*
  FStar_TypeChecker_Env.delta_level Prims.list)
  | Debug of FStar_Syntax_Syntax.term
let uu___is_Arg: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Arg _0 -> true | uu____412 -> false
let __proj__Arg__item___0:
  stack_elt -> (closure* FStar_Syntax_Syntax.aqual* FStar_Range.range) =
  fun projectee  -> match projectee with | Arg _0 -> _0
let uu___is_UnivArgs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____438 -> false
let __proj__UnivArgs__item___0:
  stack_elt -> (FStar_Syntax_Syntax.universe Prims.list* FStar_Range.range) =
  fun projectee  -> match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____464 -> false
let __proj__MemoLazy__item___0:
  stack_elt -> (env* FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo =
  fun projectee  -> match projectee with | MemoLazy _0 -> _0
let uu___is_Match: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____493 -> false
let __proj__Match__item___0: stack_elt -> (env* branches* FStar_Range.range)
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Abs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____524 -> false
let __proj__Abs__item___0:
  stack_elt ->
    (env* FStar_Syntax_Syntax.binders* env*
      (FStar_Syntax_Syntax.lcomp,FStar_Syntax_Syntax.residual_comp)
      FStar_Util.either option* FStar_Range.range)
  = fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____565 -> false
let __proj__App__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.aqual* FStar_Range.range)
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Meta: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____590 -> false
let __proj__Meta__item___0:
  stack_elt -> (FStar_Syntax_Syntax.metadata* FStar_Range.range) =
  fun projectee  -> match projectee with | Meta _0 -> _0
let uu___is_Let: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____614 -> false
let __proj__Let__item___0:
  stack_elt ->
    (env* FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.letbinding*
      FStar_Range.range)
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Steps: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Steps _0 -> true | uu____645 -> false
let __proj__Steps__item___0:
  stack_elt ->
    (steps* primitive_step Prims.list* FStar_TypeChecker_Env.delta_level
      Prims.list)
  = fun projectee  -> match projectee with | Steps _0 -> _0
let uu___is_Debug: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____674 -> false
let __proj__Debug__item___0: stack_elt -> FStar_Syntax_Syntax.term =
  fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list
let mk t r = FStar_Syntax_Syntax.mk t None r
let set_memo r t =
  let uu____730 = FStar_ST.read r in
  match uu____730 with
  | Some uu____735 -> failwith "Unexpected set_memo: thunk already evaluated"
  | None  -> FStar_ST.write r (Some t)
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____745 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____745 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___136_751  ->
    match uu___136_751 with
    | Arg (c,uu____753,uu____754) ->
        let uu____755 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____755
    | MemoLazy uu____756 -> "MemoLazy"
    | Abs (uu____760,bs,uu____762,uu____763,uu____764) ->
        let uu____771 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____771
    | UnivArgs uu____778 -> "UnivArgs"
    | Match uu____782 -> "Match"
    | App (t,uu____787,uu____788) ->
        let uu____789 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____789
    | Meta (m,uu____791) -> "Meta"
    | Let uu____792 -> "Let"
    | Steps (uu____797,uu____798,uu____799) -> "Steps"
    | Debug t ->
        let uu____805 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____805
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____812 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____812 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____828 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____828 then f () else ()
let is_empty uu___137_839 =
  match uu___137_839 with | [] -> true | uu____841 -> false
let lookup_bvar env x =
  try FStar_List.nth env x.FStar_Syntax_Syntax.index
  with
  | uu____862 ->
      let uu____863 =
        let uu____864 = FStar_Syntax_Print.db_to_string x in
        FStar_Util.format1 "Failed to find %s\n" uu____864 in
      failwith uu____863
let downgrade_ghost_effect_name:
  FStar_Ident.lident -> FStar_Ident.lident option =
  fun l  ->
    if FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Ghost_lid
    then Some FStar_Syntax_Const.effect_Pure_lid
    else
      if FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid
      then Some FStar_Syntax_Const.effect_Tot_lid
      else
        if FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid
        then Some FStar_Syntax_Const.effect_PURE_lid
        else None
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
          let uu____899 =
            FStar_List.fold_left
              (fun uu____908  ->
                 fun u1  ->
                   match uu____908 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____923 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____923 with
                        | (k_u,n1) ->
                            let uu____932 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____932
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____899 with
          | (uu____942,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____958 = FStar_List.nth env x in
                 match uu____958 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____961 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____965 ->
                   let uu____966 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____966
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____970 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____973 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____978 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____978 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____989 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____989 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____994 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____997 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____997 with
                                  | (uu____1000,m) -> n1 <= m)) in
                        if uu____994 then rest1 else us1
                    | uu____1004 -> us1)
               | uu____1007 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1010 = aux u3 in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____1010 in
        let uu____1012 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____1012
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1014 = aux u in
           match uu____1014 with
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
          (fun uu____1111  ->
             let uu____1112 = FStar_Syntax_Print.tag_of_term t in
             let uu____1113 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1112
               uu____1113);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1114 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1117 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____1138 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____1139 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____1140 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____1141 -> t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____1151 =
                    let uu____1152 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____1152 in
                  mk uu____1151 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____1159 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____1159
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____1161 = lookup_bvar env x in
                  (match uu____1161 with
                   | Univ uu____1162 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____1166) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____1234 = closures_as_binders_delayed cfg env bs in
                  (match uu____1234 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____1254 =
                         let uu____1255 =
                           let uu____1270 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____1270) in
                         FStar_Syntax_Syntax.Tm_abs uu____1255 in
                       mk uu____1254 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____1300 = closures_as_binders_delayed cfg env bs in
                  (match uu____1300 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____1331 =
                    let uu____1338 =
                      let uu____1342 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____1342] in
                    closures_as_binders_delayed cfg env uu____1338 in
                  (match uu____1331 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____1356 =
                         let uu____1357 =
                           let uu____1362 =
                             let uu____1363 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____1363
                               FStar_Pervasives.fst in
                           (uu____1362, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____1357 in
                       mk uu____1356 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____1431 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____1431
                    | FStar_Util.Inr c ->
                        let uu____1445 = close_comp cfg env c in
                        FStar_Util.Inr uu____1445 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____1460 =
                    let uu____1461 =
                      let uu____1479 = closure_as_term_delayed cfg env t11 in
                      (uu____1479, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____1461 in
                  mk uu____1460 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____1517 =
                    let uu____1518 =
                      let uu____1523 = closure_as_term_delayed cfg env t' in
                      let uu____1526 =
                        let uu____1527 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____1527 in
                      (uu____1523, uu____1526) in
                    FStar_Syntax_Syntax.Tm_meta uu____1518 in
                  mk uu____1517 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____1569 =
                    let uu____1570 =
                      let uu____1575 = closure_as_term_delayed cfg env t' in
                      let uu____1578 =
                        let uu____1579 =
                          let uu____1584 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____1584) in
                        FStar_Syntax_Syntax.Meta_monadic uu____1579 in
                      (uu____1575, uu____1578) in
                    FStar_Syntax_Syntax.Tm_meta uu____1570 in
                  mk uu____1569 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____1603 =
                    let uu____1604 =
                      let uu____1609 = closure_as_term_delayed cfg env t' in
                      let uu____1612 =
                        let uu____1613 =
                          let uu____1619 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____1619) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____1613 in
                      (uu____1609, uu____1612) in
                    FStar_Syntax_Syntax.Tm_meta uu____1604 in
                  mk uu____1603 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____1632 =
                    let uu____1633 =
                      let uu____1638 = closure_as_term_delayed cfg env t' in
                      (uu____1638, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____1633 in
                  mk uu____1632 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____1659  -> Dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let body1 =
                    match lb.FStar_Syntax_Syntax.lbname with
                    | FStar_Util.Inr uu____1670 -> body
                    | FStar_Util.Inl uu____1671 ->
                        closure_as_term cfg (Dummy :: env0) body in
                  let lb1 =
                    let uu___150_1673 = lb in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___150_1673.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___150_1673.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = typ;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___150_1673.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = def
                    } in
                  mk (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((uu____1680,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____1704  -> fun env2  -> Dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____1709 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____1709
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____1713  -> fun env2  -> Dummy :: env2) lbs
                          env_univs in
                    let uu___151_1716 = lb in
                    let uu____1717 =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let uu____1720 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___151_1716.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___151_1716.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = uu____1717;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___151_1716.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____1720
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____1731  -> fun env1  -> Dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____1786 =
                    match uu____1786 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____1832 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____1848 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____1882  ->
                                        fun uu____1883  ->
                                          match (uu____1882, uu____1883) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____1948 =
                                                norm_pat env3 p1 in
                                              (match uu____1948 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____1848 with
                               | (pats1,env3) ->
                                   ((let uu___152_2014 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.ty =
                                         (uu___152_2014.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___152_2014.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___153_2028 = x in
                                let uu____2029 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___153_2028.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___153_2028.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____2029
                                } in
                              ((let uu___154_2035 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___154_2035.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___154_2035.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___155_2040 = x in
                                let uu____2041 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___155_2040.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___155_2040.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____2041
                                } in
                              ((let uu___156_2047 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___156_2047.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___156_2047.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___157_2057 = x in
                                let uu____2058 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___157_2057.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___157_2057.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____2058
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___158_2065 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___158_2065.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___158_2065.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____2068 = norm_pat env1 pat in
                        (match uu____2068 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | None  -> None
                               | Some w ->
                                   let uu____2092 =
                                     closure_as_term cfg env2 w in
                                   Some uu____2092 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____2097 =
                    let uu____2098 =
                      let uu____2114 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____2114) in
                    FStar_Syntax_Syntax.Tm_match uu____2098 in
                  mk uu____2097 t1.FStar_Syntax_Syntax.pos))
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
        | uu____2167 -> closure_as_term cfg env t
and closures_as_args_delayed:
  cfg ->
    closure Prims.list ->
      ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax* FStar_Syntax_Syntax.aqual) Prims.list ->
        ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
          FStar_Syntax_Syntax.syntax* FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun cfg  ->
    fun env  ->
      fun args  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains CompressUvars cfg.steps)
            -> args
        | uu____2183 ->
            FStar_List.map
              (fun uu____2193  ->
                 match uu____2193 with
                 | (x,imp) ->
                     let uu____2208 = closure_as_term_delayed cfg env x in
                     (uu____2208, imp)) args
and closures_as_binders_delayed:
  cfg ->
    closure Prims.list ->
      (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list ->
        ((FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list*
          closure Prims.list)
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____2220 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____2244  ->
                  fun uu____2245  ->
                    match (uu____2244, uu____2245) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___159_2289 = b in
                          let uu____2290 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___159_2289.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___159_2289.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____2290
                          } in
                        let env2 = Dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____2220 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____2337 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____2349 = closure_as_term_delayed cfg env t in
                 let uu____2350 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____2349 uu____2350
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____2360 = closure_as_term_delayed cfg env t in
                 let uu____2361 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____2360 uu____2361
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
                        (fun uu___138_2377  ->
                           match uu___138_2377 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____2381 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____2381
                           | f -> f)) in
                 let uu____2385 =
                   let uu___160_2386 = c1 in
                   let uu____2387 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____2387;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___160_2386.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____2385)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.cflags Prims.list =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_List.filter
         (fun uu___139_2391  ->
            match uu___139_2391 with
            | FStar_Syntax_Syntax.DECREASES uu____2392 -> false
            | uu____2395 -> true))
and close_lcomp_opt:
  cfg ->
    closure Prims.list ->
      (FStar_Syntax_Syntax.lcomp,(FStar_Ident.lident*
                                   FStar_Syntax_Syntax.cflags Prims.list))
        FStar_Util.either option ->
        (FStar_Syntax_Syntax.lcomp,(FStar_Ident.lident*
                                     FStar_Syntax_Syntax.cflags Prims.list))
          FStar_Util.either option
  =
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | Some (FStar_Util.Inl lc) ->
            let flags = filter_out_lcomp_cflags lc in
            let uu____2423 = FStar_Syntax_Util.is_total_lcomp lc in
            if uu____2423
            then
              Some
                (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, flags))
            else
              (let uu____2440 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
               if uu____2440
               then
                 Some
                   (FStar_Util.Inr
                      (FStar_Syntax_Const.effect_GTot_lid, flags))
               else
                 Some
                   (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags)))
        | uu____2466 -> lopt
let built_in_primitive_steps: primitive_step Prims.list =
  let const_as_tm c p = mk (FStar_Syntax_Syntax.Tm_constant c) p in
  let int_as_const p i =
    let uu____2490 =
      let uu____2491 =
        let uu____2497 = FStar_Util.string_of_int i in (uu____2497, None) in
      FStar_Const.Const_int uu____2491 in
    const_as_tm uu____2490 p in
  let bool_as_const p b = const_as_tm (FStar_Const.Const_bool b) p in
  let string_as_const p b =
    const_as_tm
      (FStar_Const.Const_string ((FStar_Util.bytes_of_string b), p)) p in
  let arg_as_int uu____2524 =
    match uu____2524 with
    | (a,uu____2529) ->
        let uu____2531 =
          let uu____2532 = FStar_Syntax_Subst.compress a in
          uu____2532.FStar_Syntax_Syntax.n in
        (match uu____2531 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i,None ))
             ->
             let uu____2542 = FStar_Util.int_of_string i in Some uu____2542
         | uu____2543 -> None) in
  let arg_as_bounded_int uu____2552 =
    match uu____2552 with
    | (a,uu____2559) ->
        let uu____2563 =
          let uu____2564 = FStar_Syntax_Subst.compress a in
          uu____2564.FStar_Syntax_Syntax.n in
        (match uu____2563 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.tk = uu____2571;
                FStar_Syntax_Syntax.pos = uu____2572;
                FStar_Syntax_Syntax.vars = uu____2573;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,None ));
                                                            FStar_Syntax_Syntax.tk
                                                              = uu____2575;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____2576;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____2577;_},uu____2578)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____2609 =
               let uu____2612 = FStar_Util.int_of_string i in
               (fv1, uu____2612) in
             Some uu____2609
         | uu____2615 -> None) in
  let arg_as_bool uu____2624 =
    match uu____2624 with
    | (a,uu____2629) ->
        let uu____2631 =
          let uu____2632 = FStar_Syntax_Subst.compress a in
          uu____2632.FStar_Syntax_Syntax.n in
        (match uu____2631 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
             Some b
         | uu____2637 -> None) in
  let arg_as_char uu____2644 =
    match uu____2644 with
    | (a,uu____2649) ->
        let uu____2651 =
          let uu____2652 = FStar_Syntax_Subst.compress a in
          uu____2652.FStar_Syntax_Syntax.n in
        (match uu____2651 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
             Some c
         | uu____2657 -> None) in
  let arg_as_string uu____2664 =
    match uu____2664 with
    | (a,uu____2669) ->
        let uu____2671 =
          let uu____2672 = FStar_Syntax_Subst.compress a in
          uu____2672.FStar_Syntax_Syntax.n in
        (match uu____2671 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (bytes,uu____2677)) -> Some (FStar_Util.string_of_bytes bytes)
         | uu____2680 -> None) in
  let arg_as_list f uu____2701 =
    match uu____2701 with
    | (a,uu____2710) ->
        let rec sequence l =
          match l with
          | [] -> Some []
          | (None )::uu____2729 -> None
          | (Some x)::xs ->
              let uu____2739 = sequence xs in
              (match uu____2739 with
               | None  -> None
               | Some xs' -> Some (x :: xs')) in
        let uu____2750 = FStar_Syntax_Util.list_elements a in
        (match uu____2750 with
         | None  -> None
         | Some elts ->
             let uu____2760 =
               FStar_List.map
                 (fun x  ->
                    let uu____2765 = FStar_Syntax_Syntax.as_arg x in
                    f uu____2765) elts in
             sequence uu____2760) in
  let lift_unary f aopts =
    match aopts with
    | (Some a)::[] -> let uu____2795 = f a in Some uu____2795
    | uu____2796 -> None in
  let lift_binary f aopts =
    match aopts with
    | (Some a0)::(Some a1)::[] -> let uu____2835 = f a0 a1 in Some uu____2835
    | uu____2836 -> None in
  let unary_op as_a f r args =
    let uu____2880 = FStar_List.map as_a args in lift_unary (f r) uu____2880 in
  let binary_op as_a f r args =
    let uu____2930 = FStar_List.map as_a args in lift_binary (f r) uu____2930 in
  let as_primitive_step uu____2947 =
    match uu____2947 with
    | (l,arity,f) ->
        { name = l; arity; strong_reduction_ok = true; interpretation = f } in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  -> fun x  -> let uu____2985 = f x in int_as_const r uu____2985) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  -> let uu____3008 = f x y in int_as_const r uu____3008) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  -> fun x  -> let uu____3025 = f x in bool_as_const r uu____3025) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  -> let uu____3048 = f x y in bool_as_const r uu____3048) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  -> let uu____3071 = f x y in string_as_const r uu____3071) in
  let list_of_string' rng s =
    let name l =
      let uu____3085 =
        let uu____3086 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            None in
        FStar_Syntax_Syntax.Tm_fvar uu____3086 in
      mk uu____3085 rng in
    let char_t = name FStar_Syntax_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____3096 =
      let uu____3098 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____3098 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____3096 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Const.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in int_as_const rng r in
  let string_concat' rng args =
    match args with
    | a1::a2::[] ->
        let uu____3152 = arg_as_string a1 in
        (match uu____3152 with
         | Some s1 ->
             let uu____3156 = arg_as_list arg_as_string a2 in
             (match uu____3156 with
              | Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____3164 = string_as_const rng r in Some uu____3164
              | uu____3165 -> None)
         | uu____3168 -> None)
    | uu____3170 -> None in
  let string_of_int1 rng i =
    let uu____3181 = FStar_Util.string_of_int i in
    string_as_const rng uu____3181 in
  let string_of_bool1 rng b =
    string_as_const rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____3197 = FStar_Util.string_of_int i in
    string_as_const rng uu____3197 in
  let string_of_bool2 rng b =
    string_as_const rng (if b then "true" else "false") in
  let basic_ops =
    let uu____3216 =
      let uu____3226 =
        let uu____3236 =
          let uu____3246 =
            let uu____3256 =
              let uu____3266 =
                let uu____3276 =
                  let uu____3286 =
                    let uu____3296 =
                      let uu____3306 =
                        let uu____3316 =
                          let uu____3326 =
                            let uu____3336 =
                              let uu____3346 =
                                let uu____3356 =
                                  let uu____3366 =
                                    let uu____3376 =
                                      let uu____3386 =
                                        let uu____3395 =
                                          FStar_Syntax_Const.p2l
                                            ["FStar";
                                            "String";
                                            "list_of_string"] in
                                        (uu____3395, (Prims.parse_int "1"),
                                          (unary_op arg_as_string
                                             list_of_string')) in
                                      let uu____3401 =
                                        let uu____3411 =
                                          let uu____3420 =
                                            FStar_Syntax_Const.p2l
                                              ["FStar";
                                              "String";
                                              "string_of_list"] in
                                          (uu____3420, (Prims.parse_int "1"),
                                            (unary_op
                                               (arg_as_list arg_as_char)
                                               string_of_list')) in
                                        let uu____3427 =
                                          let uu____3437 =
                                            let uu____3449 =
                                              FStar_Syntax_Const.p2l
                                                ["FStar"; "String"; "concat"] in
                                            (uu____3449,
                                              (Prims.parse_int "2"),
                                              string_concat') in
                                          [uu____3437] in
                                        uu____3411 :: uu____3427 in
                                      uu____3386 :: uu____3401 in
                                    (FStar_Syntax_Const.string_compare,
                                      (Prims.parse_int "2"),
                                      (binary_op arg_as_string
                                         string_compare'))
                                      :: uu____3376 in
                                  (FStar_Syntax_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_bool string_of_bool2))
                                    :: uu____3366 in
                                (FStar_Syntax_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (unary_op arg_as_int string_of_int2)) ::
                                  uu____3356 in
                              (FStar_Syntax_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____3346 in
                            (FStar_Syntax_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____3336 in
                          (FStar_Syntax_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____3326 in
                        (FStar_Syntax_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____3316 in
                      (FStar_Syntax_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____3306 in
                    (FStar_Syntax_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
                      :: uu____3296 in
                  (FStar_Syntax_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____3286 in
                (FStar_Syntax_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____3276 in
              (FStar_Syntax_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____3266 in
            (FStar_Syntax_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____3256 in
          (FStar_Syntax_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____3246 in
        (FStar_Syntax_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____3236 in
      (FStar_Syntax_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____3226 in
    (FStar_Syntax_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____3216 in
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
      let uu____3773 =
        let uu____3774 =
          let uu____3775 = FStar_Syntax_Syntax.as_arg c in [uu____3775] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____3774 in
      uu____3773 None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____3799 =
              let uu____3808 = FStar_Syntax_Const.p2l ["FStar"; m; "add"] in
              (uu____3808, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____3817  ->
                        fun uu____3818  ->
                          match (uu____3817, uu____3818) with
                          | ((int_to_t1,x),(uu____3829,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____3835 =
              let uu____3845 =
                let uu____3854 = FStar_Syntax_Const.p2l ["FStar"; m; "sub"] in
                (uu____3854, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____3863  ->
                          fun uu____3864  ->
                            match (uu____3863, uu____3864) with
                            | ((int_to_t1,x),(uu____3875,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____3881 =
                let uu____3891 =
                  let uu____3900 = FStar_Syntax_Const.p2l ["FStar"; m; "mul"] in
                  (uu____3900, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____3909  ->
                            fun uu____3910  ->
                              match (uu____3909, uu____3910) with
                              | ((int_to_t1,x),(uu____3921,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____3891] in
              uu____3845 :: uu____3881 in
            uu____3799 :: uu____3835)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_bool neg rng args =
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) rng in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) rng in
    match args with
    | (_typ,uu____3996)::(a1,uu____3998)::(a2,uu____4000)::[] ->
        let uu____4029 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4029 with
         | FStar_Syntax_Util.Equal  -> Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  -> Some (if neg then tru else fal)
         | uu____4041 -> None)
    | uu____4042 -> failwith "Unexpected number of arguments" in
  let interp_prop r args =
    match args with
    | (_typ,uu____4055)::(a1,uu____4057)::(a2,uu____4059)::[] ->
        let uu____4088 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4088 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___161_4092 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___161_4092.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___161_4092.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___161_4092.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___162_4099 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___162_4099.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___162_4099.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___162_4099.FStar_Syntax_Syntax.vars)
                })
         | uu____4104 -> None)
    | (_typ,uu____4106)::uu____4107::(a1,uu____4109)::(a2,uu____4111)::[] ->
        let uu____4148 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4148 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___161_4152 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___161_4152.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___161_4152.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___161_4152.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___162_4159 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___162_4159.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___162_4159.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___162_4159.FStar_Syntax_Syntax.vars)
                })
         | uu____4164 -> None)
    | uu____4165 -> failwith "Unexpected number of arguments" in
  let decidable_equality =
    [{
       name = FStar_Syntax_Const.op_Eq;
       arity = (Prims.parse_int "3");
       strong_reduction_ok = true;
       interpretation = (interp_bool false)
     };
    {
      name = FStar_Syntax_Const.op_notEq;
      arity = (Prims.parse_int "3");
      strong_reduction_ok = true;
      interpretation = (interp_bool true)
    }] in
  let propositional_equality =
    {
      name = FStar_Syntax_Const.eq2_lid;
      arity = (Prims.parse_int "3");
      strong_reduction_ok = true;
      interpretation = interp_prop
    } in
  let hetero_propositional_equality =
    {
      name = FStar_Syntax_Const.eq3_lid;
      arity = (Prims.parse_int "4");
      strong_reduction_ok = true;
      interpretation = interp_prop
    } in
  FStar_List.append decidable_equality
    [propositional_equality; hetero_propositional_equality]
let reduce_primops:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      let uu____4179 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops cfg.steps) in
      if uu____4179
      then tm
      else
        (let uu____4181 = FStar_Syntax_Util.head_and_args tm in
         match uu____4181 with
         | (head1,args) ->
             let uu____4207 =
               let uu____4208 = FStar_Syntax_Util.un_uinst head1 in
               uu____4208.FStar_Syntax_Syntax.n in
             (match uu____4207 with
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____4212 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps in
                  (match uu____4212 with
                   | None  -> tm
                   | Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then tm
                       else
                         (let uu____4227 =
                            prim_step.interpretation
                              head1.FStar_Syntax_Syntax.pos args in
                          match uu____4227 with
                          | None  -> tm
                          | Some reduced -> reduced))
              | uu____4230 -> tm))
let reduce_equality:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___163_4239 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___163_4239.tcenv);
           delta_level = (uu___163_4239.delta_level);
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
        let uu___164_4263 = t in
        {
          FStar_Syntax_Syntax.n = (uu___164_4263.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___164_4263.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___164_4263.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid ->
            Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid ->
            Some false
        | uu____4282 -> None in
      let simplify arg = ((simp_t (fst arg)), arg) in
      let tm1 = reduce_primops cfg tm in
      let uu____4310 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps) in
      if uu____4310
      then tm1
      else
        (match tm1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.tk = uu____4313;
                     FStar_Syntax_Syntax.pos = uu____4314;
                     FStar_Syntax_Syntax.vars = uu____4315;_},uu____4316);
                FStar_Syntax_Syntax.tk = uu____4317;
                FStar_Syntax_Syntax.pos = uu____4318;
                FStar_Syntax_Syntax.vars = uu____4319;_},args)
             ->
             let uu____4339 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____4339
             then
               let uu____4340 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____4340 with
                | (Some (true ),uu____4373)::(uu____4374,(arg,uu____4376))::[]
                    -> arg
                | (uu____4417,(arg,uu____4419))::(Some (true ),uu____4420)::[]
                    -> arg
                | (Some (false ),uu____4461)::uu____4462::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4500::(Some (false ),uu____4501)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4539 -> tm1)
             else
               (let uu____4549 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____4549
                then
                  let uu____4550 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____4550 with
                  | (Some (true ),uu____4583)::uu____4584::[] ->
                      w FStar_Syntax_Util.t_true
                  | uu____4622::(Some (true ),uu____4623)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),uu____4661)::(uu____4662,(arg,uu____4664))::[]
                      -> arg
                  | (uu____4705,(arg,uu____4707))::(Some (false ),uu____4708)::[]
                      -> arg
                  | uu____4749 -> tm1
                else
                  (let uu____4759 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____4759
                   then
                     let uu____4760 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____4760 with
                     | uu____4793::(Some (true ),uu____4794)::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (false ),uu____4832)::uu____4833::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____4871)::(uu____4872,(arg,uu____4874))::[]
                         -> arg
                     | (uu____4915,(p,uu____4917))::(uu____4918,(q,uu____4920))::[]
                         ->
                         let uu____4962 = FStar_Syntax_Util.term_eq p q in
                         (if uu____4962
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____4964 -> tm1
                   else
                     (let uu____4974 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____4974
                      then
                        let uu____4975 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____4975 with
                        | (Some (true ),uu____5008)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____5032)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____5056 -> tm1
                      else
                        (let uu____5066 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid in
                         if uu____5066
                         then
                           match args with
                           | (t,uu____5068)::[] ->
                               let uu____5081 =
                                 let uu____5082 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5082.FStar_Syntax_Syntax.n in
                               (match uu____5081 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5085::[],body,uu____5087) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5113 -> tm1)
                                | uu____5115 -> tm1)
                           | (uu____5116,Some (FStar_Syntax_Syntax.Implicit
                              uu____5117))::(t,uu____5119)::[] ->
                               let uu____5146 =
                                 let uu____5147 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5147.FStar_Syntax_Syntax.n in
                               (match uu____5146 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5150::[],body,uu____5152) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5178 -> tm1)
                                | uu____5180 -> tm1)
                           | uu____5181 -> tm1
                         else
                           (let uu____5188 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid in
                            if uu____5188
                            then
                              match args with
                              | (t,uu____5190)::[] ->
                                  let uu____5203 =
                                    let uu____5204 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5204.FStar_Syntax_Syntax.n in
                                  (match uu____5203 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5207::[],body,uu____5209) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5235 -> tm1)
                                   | uu____5237 -> tm1)
                              | (uu____5238,Some
                                 (FStar_Syntax_Syntax.Implicit uu____5239))::
                                  (t,uu____5241)::[] ->
                                  let uu____5268 =
                                    let uu____5269 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5269.FStar_Syntax_Syntax.n in
                                  (match uu____5268 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5272::[],body,uu____5274) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5300 -> tm1)
                                   | uu____5302 -> tm1)
                              | uu____5303 -> tm1
                            else reduce_equality cfg tm1)))))
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                FStar_Syntax_Syntax.tk = uu____5311;
                FStar_Syntax_Syntax.pos = uu____5312;
                FStar_Syntax_Syntax.vars = uu____5313;_},args)
             ->
             let uu____5329 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____5329
             then
               let uu____5330 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____5330 with
                | (Some (true ),uu____5363)::(uu____5364,(arg,uu____5366))::[]
                    -> arg
                | (uu____5407,(arg,uu____5409))::(Some (true ),uu____5410)::[]
                    -> arg
                | (Some (false ),uu____5451)::uu____5452::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____5490::(Some (false ),uu____5491)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____5529 -> tm1)
             else
               (let uu____5539 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____5539
                then
                  let uu____5540 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____5540 with
                  | (Some (true ),uu____5573)::uu____5574::[] ->
                      w FStar_Syntax_Util.t_true
                  | uu____5612::(Some (true ),uu____5613)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),uu____5651)::(uu____5652,(arg,uu____5654))::[]
                      -> arg
                  | (uu____5695,(arg,uu____5697))::(Some (false ),uu____5698)::[]
                      -> arg
                  | uu____5739 -> tm1
                else
                  (let uu____5749 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____5749
                   then
                     let uu____5750 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____5750 with
                     | uu____5783::(Some (true ),uu____5784)::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (false ),uu____5822)::uu____5823::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____5861)::(uu____5862,(arg,uu____5864))::[]
                         -> arg
                     | (uu____5905,(p,uu____5907))::(uu____5908,(q,uu____5910))::[]
                         ->
                         let uu____5952 = FStar_Syntax_Util.term_eq p q in
                         (if uu____5952
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____5954 -> tm1
                   else
                     (let uu____5964 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____5964
                      then
                        let uu____5965 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____5965 with
                        | (Some (true ),uu____5998)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____6022)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____6046 -> tm1
                      else
                        (let uu____6056 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid in
                         if uu____6056
                         then
                           match args with
                           | (t,uu____6058)::[] ->
                               let uu____6071 =
                                 let uu____6072 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____6072.FStar_Syntax_Syntax.n in
                               (match uu____6071 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____6075::[],body,uu____6077) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____6103 -> tm1)
                                | uu____6105 -> tm1)
                           | (uu____6106,Some (FStar_Syntax_Syntax.Implicit
                              uu____6107))::(t,uu____6109)::[] ->
                               let uu____6136 =
                                 let uu____6137 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____6137.FStar_Syntax_Syntax.n in
                               (match uu____6136 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____6140::[],body,uu____6142) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____6168 -> tm1)
                                | uu____6170 -> tm1)
                           | uu____6171 -> tm1
                         else
                           (let uu____6178 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid in
                            if uu____6178
                            then
                              match args with
                              | (t,uu____6180)::[] ->
                                  let uu____6193 =
                                    let uu____6194 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____6194.FStar_Syntax_Syntax.n in
                                  (match uu____6193 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6197::[],body,uu____6199) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____6225 -> tm1)
                                   | uu____6227 -> tm1)
                              | (uu____6228,Some
                                 (FStar_Syntax_Syntax.Implicit uu____6229))::
                                  (t,uu____6231)::[] ->
                                  let uu____6258 =
                                    let uu____6259 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____6259.FStar_Syntax_Syntax.n in
                                  (match uu____6258 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6262::[],body,uu____6264) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____6290 -> tm1)
                                   | uu____6292 -> tm1)
                              | uu____6293 -> tm1
                            else reduce_equality cfg tm1)))))
         | uu____6300 -> tm1)
let is_norm_request hd1 args =
  let uu____6318 =
    let uu____6322 =
      let uu____6323 = FStar_Syntax_Util.un_uinst hd1 in
      uu____6323.FStar_Syntax_Syntax.n in
    (uu____6322, args) in
  match uu____6318 with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6328::uu____6329::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize_term
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6332::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize
  | uu____6334 -> false
let get_norm_request args =
  match args with
  | uu____6356::(tm,uu____6358)::[] -> tm
  | (tm,uu____6368)::[] -> tm
  | uu____6373 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___140_6381  ->
    match uu___140_6381 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.tk = uu____6383;
           FStar_Syntax_Syntax.pos = uu____6384;
           FStar_Syntax_Syntax.vars = uu____6385;_},uu____6386,uu____6387))::uu____6388
        -> true
    | uu____6394 -> false
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
            (fun uu____6512  ->
               let uu____6513 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____6514 = FStar_Syntax_Print.term_to_string t1 in
               let uu____6515 =
                 let uu____6516 =
                   let uu____6518 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives.fst uu____6518 in
                 stack_to_string uu____6516 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____6513
                 uu____6514 uu____6515);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____6530 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____6551 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____6560 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____6561 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6562;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____6563;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6568;
                 FStar_Syntax_Syntax.fv_delta = uu____6569;
                 FStar_Syntax_Syntax.fv_qual = Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6573;
                 FStar_Syntax_Syntax.fv_delta = uu____6574;
                 FStar_Syntax_Syntax.fv_qual = Some
                   (FStar_Syntax_Syntax.Record_ctor uu____6575);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (FStar_Syntax_Util.is_fstar_tactics_embed hd1) ||
                 (FStar_Syntax_Util.is_fstar_tactics_by_tactic hd1)
               ->
               let args1 = closures_as_args_delayed cfg env args in
               let hd2 = closure_as_term cfg env hd1 in
               let t2 =
                 let uu___165_6608 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.tk =
                     (uu___165_6608.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___165_6608.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___165_6608.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____6634 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____6634) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Syntax_Const.prims_lid))
               ->
               let tm = get_norm_request args in
               let s =
                 [Reify;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 Primops] in
               let cfg' =
                 let uu___166_6647 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___166_6647.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___166_6647.primitive_steps)
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
                  FStar_Syntax_Syntax.tk = uu____6652;
                  FStar_Syntax_Syntax.pos = uu____6653;
                  FStar_Syntax_Syntax.vars = uu____6654;_},a1::a2::rest)
               ->
               let uu____6688 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6688 with
                | (hd1,uu____6699) ->
                    let t' =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_app (hd1, [a1])) None
                        t1.FStar_Syntax_Syntax.pos in
                    let t2 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_app (t', (a2 :: rest))) None
                        t1.FStar_Syntax_Syntax.pos in
                    norm cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect uu____6754);
                  FStar_Syntax_Syntax.tk = uu____6755;
                  FStar_Syntax_Syntax.pos = uu____6756;
                  FStar_Syntax_Syntax.vars = uu____6757;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____6780 = FStar_List.tl stack1 in
               norm cfg env uu____6780 (fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.tk = uu____6783;
                  FStar_Syntax_Syntax.pos = uu____6784;
                  FStar_Syntax_Syntax.vars = uu____6785;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____6808 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6808 with
                | (reify_head,uu____6819) ->
                    let a1 =
                      let uu____6835 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (fst a) in
                      FStar_Syntax_Subst.compress uu____6835 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____6838);
                            FStar_Syntax_Syntax.tk = uu____6839;
                            FStar_Syntax_Syntax.pos = uu____6840;
                            FStar_Syntax_Syntax.vars = uu____6841;_},a2::[])
                         -> norm cfg env stack1 (fst a2)
                     | uu____6866 ->
                         let stack2 =
                           (App
                              (reify_head, None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____6874 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____6874
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____6881 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____6881
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____6884 =
                      let uu____6888 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____6888, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____6884 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___141_6897  ->
                         match uu___141_6897 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____6900 =
                   (FStar_List.mem FStar_TypeChecker_Env.UnfoldTac
                      cfg.delta_level)
                     &&
                     (((((((((FStar_Syntax_Syntax.fv_eq_lid f
                                FStar_Syntax_Const.and_lid)
                               ||
                               (FStar_Syntax_Syntax.fv_eq_lid f
                                  FStar_Syntax_Const.or_lid))
                              ||
                              (FStar_Syntax_Syntax.fv_eq_lid f
                                 FStar_Syntax_Const.imp_lid))
                             ||
                             (FStar_Syntax_Syntax.fv_eq_lid f
                                FStar_Syntax_Const.forall_lid))
                            ||
                            (FStar_Syntax_Syntax.fv_eq_lid f
                               FStar_Syntax_Const.squash_lid))
                           ||
                           (FStar_Syntax_Syntax.fv_eq_lid f
                              FStar_Syntax_Const.exists_lid))
                          ||
                          (FStar_Syntax_Syntax.fv_eq_lid f
                             FStar_Syntax_Const.eq2_lid))
                         ||
                         (FStar_Syntax_Syntax.fv_eq_lid f
                            FStar_Syntax_Const.true_lid))
                        ||
                        (FStar_Syntax_Syntax.fv_eq_lid f
                           FStar_Syntax_Const.false_lid)) in
                 if uu____6900 then false else should_delta in
               if Prims.op_Negation should_delta1
               then rebuild cfg env stack1 t1
               else
                 (let r_env =
                    let uu____6904 = FStar_Syntax_Syntax.range_of_fv f in
                    FStar_TypeChecker_Env.set_range cfg.tcenv uu____6904 in
                  let uu____6905 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  match uu____6905 with
                  | None  ->
                      (log cfg
                         (fun uu____6916  ->
                            FStar_Util.print "Tm_fvar case 2\n" []);
                       rebuild cfg env stack1 t1)
                  | Some (us,t2) ->
                      (log cfg
                         (fun uu____6922  ->
                            let uu____6923 =
                              FStar_Syntax_Print.term_to_string t0 in
                            let uu____6924 =
                              FStar_Syntax_Print.term_to_string t2 in
                            FStar_Util.print2 ">>> Unfolded %s to %s\n"
                              uu____6923 uu____6924);
                       (let t3 =
                          let uu____6926 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 (UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant)) in
                          if uu____6926
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
                          | (UnivArgs (us',uu____6942))::stack2 ->
                              let env1 =
                                FStar_All.pipe_right us'
                                  (FStar_List.fold_left
                                     (fun env1  -> fun u  -> (Univ u) :: env1)
                                     env) in
                              norm cfg env1 stack2 t3
                          | uu____6955 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack1 t3
                          | uu____6956 ->
                              let uu____6957 =
                                let uu____6958 =
                                  FStar_Syntax_Print.lid_to_string
                                    (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                FStar_Util.format1
                                  "Impossible: missing universe instantiation on %s"
                                  uu____6958 in
                              failwith uu____6957
                        else norm cfg env stack1 t3)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____6965 = lookup_bvar env x in
               (match uu____6965 with
                | Univ uu____6966 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____6981 = FStar_ST.read r in
                      (match uu____6981 with
                       | Some (env2,t') ->
                           (log cfg
                              (fun uu____7000  ->
                                 let uu____7001 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____7002 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____7001
                                   uu____7002);
                            (let uu____7003 =
                               let uu____7004 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____7004.FStar_Syntax_Syntax.n in
                             match uu____7003 with
                             | FStar_Syntax_Syntax.Tm_abs uu____7007 ->
                                 norm cfg env2 stack1 t'
                             | uu____7022 -> rebuild cfg env2 stack1 t'))
                       | None  -> norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____7055)::uu____7056 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____7061)::uu____7062 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____7068,uu____7069))::stack_rest ->
                    (match c with
                     | Univ uu____7072 -> norm cfg (c :: env) stack_rest t1
                     | uu____7073 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____7076::[] ->
                              (match lopt with
                               | None  when FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____7089  ->
                                         let uu____7090 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____7090);
                                    norm cfg (c :: env) stack_rest body)
                               | Some (FStar_Util.Inr (l,cflags)) when
                                   ((FStar_Ident.lid_equals l
                                       FStar_Syntax_Const.effect_Tot_lid)
                                      ||
                                      (FStar_Ident.lid_equals l
                                         FStar_Syntax_Const.effect_GTot_lid))
                                     ||
                                     (FStar_All.pipe_right cflags
                                        (FStar_Util.for_some
                                           (fun uu___142_7104  ->
                                              match uu___142_7104 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____7105 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____7107  ->
                                         let uu____7108 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____7108);
                                    norm cfg (c :: env) stack_rest body)
                               | Some (FStar_Util.Inl lc) when
                                   FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                                   ->
                                   (log cfg
                                      (fun uu____7119  ->
                                         let uu____7120 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____7120);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____7121 when
                                   FStar_All.pipe_right cfg.steps
                                     (FStar_List.contains Reify)
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____7128 ->
                                   let cfg1 =
                                     let uu___167_7136 = cfg in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___167_7136.tcenv);
                                       delta_level =
                                         (uu___167_7136.delta_level);
                                       primitive_steps =
                                         (uu___167_7136.primitive_steps)
                                     } in
                                   let uu____7137 =
                                     closure_as_term cfg1 env t1 in
                                   rebuild cfg1 env stack1 uu____7137)
                          | uu____7138::tl1 ->
                              (log cfg
                                 (fun uu____7148  ->
                                    let uu____7149 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____7149);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___168_7173 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___168_7173.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____7186  ->
                          let uu____7187 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____7187);
                     norm cfg env stack2 t1)
                | (Debug uu____7188)::uu____7189 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7191 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7191
                    else
                      (let uu____7193 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7193 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7222 =
                                   let uu____7228 =
                                     let uu____7229 =
                                       let uu____7230 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7230 in
                                     FStar_All.pipe_right uu____7229
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7228
                                     (fun _0_41  -> FStar_Util.Inl _0_41) in
                                 FStar_All.pipe_right uu____7222
                                   (fun _0_42  -> Some _0_42)
                             | uu____7255 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7269  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7274  ->
                                 let uu____7275 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7275);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7287 = cfg in
                               let uu____7288 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7287.steps);
                                 tcenv = (uu___169_7287.tcenv);
                                 delta_level = (uu___169_7287.delta_level);
                                 primitive_steps = uu____7288
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____7298)::uu____7299 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7303 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7303
                    else
                      (let uu____7305 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7305 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7334 =
                                   let uu____7340 =
                                     let uu____7341 =
                                       let uu____7342 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7342 in
                                     FStar_All.pipe_right uu____7341
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7340
                                     (fun _0_43  -> FStar_Util.Inl _0_43) in
                                 FStar_All.pipe_right uu____7334
                                   (fun _0_44  -> Some _0_44)
                             | uu____7367 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7381  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7386  ->
                                 let uu____7387 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7387);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7399 = cfg in
                               let uu____7400 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7399.steps);
                                 tcenv = (uu___169_7399.tcenv);
                                 delta_level = (uu___169_7399.delta_level);
                                 primitive_steps = uu____7400
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____7410)::uu____7411 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7417 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7417
                    else
                      (let uu____7419 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7419 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7448 =
                                   let uu____7454 =
                                     let uu____7455 =
                                       let uu____7456 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7456 in
                                     FStar_All.pipe_right uu____7455
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7454
                                     (fun _0_45  -> FStar_Util.Inl _0_45) in
                                 FStar_All.pipe_right uu____7448
                                   (fun _0_46  -> Some _0_46)
                             | uu____7481 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7495  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7500  ->
                                 let uu____7501 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7501);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7513 = cfg in
                               let uu____7514 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7513.steps);
                                 tcenv = (uu___169_7513.tcenv);
                                 delta_level = (uu___169_7513.delta_level);
                                 primitive_steps = uu____7514
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____7524)::uu____7525 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7530 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7530
                    else
                      (let uu____7532 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7532 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7561 =
                                   let uu____7567 =
                                     let uu____7568 =
                                       let uu____7569 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7569 in
                                     FStar_All.pipe_right uu____7568
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7567
                                     (fun _0_47  -> FStar_Util.Inl _0_47) in
                                 FStar_All.pipe_right uu____7561
                                   (fun _0_48  -> Some _0_48)
                             | uu____7594 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7608  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7613  ->
                                 let uu____7614 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7614);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7626 = cfg in
                               let uu____7627 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7626.steps);
                                 tcenv = (uu___169_7626.tcenv);
                                 delta_level = (uu___169_7626.delta_level);
                                 primitive_steps = uu____7627
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____7637)::uu____7638 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7648 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7648
                    else
                      (let uu____7650 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7650 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7679 =
                                   let uu____7685 =
                                     let uu____7686 =
                                       let uu____7687 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7687 in
                                     FStar_All.pipe_right uu____7686
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7685
                                     (fun _0_49  -> FStar_Util.Inl _0_49) in
                                 FStar_All.pipe_right uu____7679
                                   (fun _0_50  -> Some _0_50)
                             | uu____7712 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7726  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7731  ->
                                 let uu____7732 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7732);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7744 = cfg in
                               let uu____7745 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7744.steps);
                                 tcenv = (uu___169_7744.tcenv);
                                 delta_level = (uu___169_7744.delta_level);
                                 primitive_steps = uu____7745
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7755 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7755
                    else
                      (let uu____7757 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7757 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7786 =
                                   let uu____7792 =
                                     let uu____7793 =
                                       let uu____7794 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7794 in
                                     FStar_All.pipe_right uu____7793
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7792
                                     (fun _0_51  -> FStar_Util.Inl _0_51) in
                                 FStar_All.pipe_right uu____7786
                                   (fun _0_52  -> Some _0_52)
                             | uu____7819 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7833  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7838  ->
                                 let uu____7839 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7839);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7851 = cfg in
                               let uu____7852 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7851.steps);
                                 tcenv = (uu___169_7851.tcenv);
                                 delta_level = (uu___169_7851.delta_level);
                                 primitive_steps = uu____7852
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
                      (fun uu____7884  ->
                         fun stack2  ->
                           match uu____7884 with
                           | (a,aq) ->
                               let uu____7892 =
                                 let uu____7893 =
                                   let uu____7897 =
                                     let uu____7898 =
                                       let uu____7908 =
                                         FStar_Util.mk_ref None in
                                       (env, a, uu____7908, false) in
                                     Clos uu____7898 in
                                   (uu____7897, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____7893 in
                               uu____7892 :: stack2) args) in
               (log cfg
                  (fun uu____7930  ->
                     let uu____7931 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____7931);
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
                             ((let uu___170_7954 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___170_7954.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___170_7954.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____7955 ->
                      let uu____7958 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7958)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____7961 = FStar_Syntax_Subst.open_term [(x, None)] f in
                  match uu____7961 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____7977 =
                          let uu____7978 =
                            let uu____7983 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___171_7984 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___171_7984.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___171_7984.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____7983) in
                          FStar_Syntax_Syntax.Tm_refine uu____7978 in
                        mk uu____7977 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____7997 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____7997
               else
                 (let uu____7999 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____7999 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____8005 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  -> fun uu____8011  -> Dummy :: env1)
                               env) in
                        norm_comp cfg uu____8005 c1 in
                      let t2 =
                        let uu____8018 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____8018 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____8061)::uu____8062 -> norm cfg env stack1 t11
                | (Arg uu____8067)::uu____8068 -> norm cfg env stack1 t11
                | (App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.tk = uu____8073;
                       FStar_Syntax_Syntax.pos = uu____8074;
                       FStar_Syntax_Syntax.vars = uu____8075;_},uu____8076,uu____8077))::uu____8078
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____8084)::uu____8085 ->
                    norm cfg env stack1 t11
                | uu____8090 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____8093  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____8106 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____8106
                        | FStar_Util.Inr c ->
                            let uu____8114 = norm_comp cfg env c in
                            FStar_Util.Inr uu____8114 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____8119 =
                        mk
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (t12, (tc1, tacopt1), l))
                          t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____8119)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____8170,{
                              FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                uu____8171;
                              FStar_Syntax_Syntax.lbunivs = uu____8172;
                              FStar_Syntax_Syntax.lbtyp = uu____8173;
                              FStar_Syntax_Syntax.lbeff = uu____8174;
                              FStar_Syntax_Syntax.lbdef = uu____8175;_}::uu____8176),uu____8177)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____8203 =
                 (let uu____8204 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____8204) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____8205 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____8205))) in
               if uu____8203
               then
                 let env1 =
                   let uu____8208 =
                     let uu____8209 =
                       let uu____8219 = FStar_Util.mk_ref None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____8219,
                         false) in
                     Clos uu____8209 in
                   uu____8208 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____8243 =
                    let uu____8246 =
                      let uu____8247 =
                        let uu____8248 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____8248
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____8247] in
                    FStar_Syntax_Subst.open_term uu____8246 body in
                  match uu____8243 with
                  | (bs,body1) ->
                      let lb1 =
                        let uu___172_8254 = lb in
                        let uu____8255 =
                          let uu____8258 =
                            let uu____8259 = FStar_List.hd bs in
                            FStar_All.pipe_right uu____8259
                              FStar_Pervasives.fst in
                          FStar_All.pipe_right uu____8258
                            (fun _0_53  -> FStar_Util.Inl _0_53) in
                        let uu____8268 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____8271 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = uu____8255;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___172_8254.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____8268;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___172_8254.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____8271
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____8281  -> Dummy :: env1)
                             env) in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____8297 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____8297
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____8310 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____8332  ->
                        match uu____8332 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____8371 =
                                let uu___173_8372 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___173_8372.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___173_8372.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____8371 in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos in
                            let memo = FStar_Util.mk_ref None in
                            let rec_env1 = (Clos (env, fix_f_i, memo, true))
                              :: rec_env in
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1")))) (snd lbs)
                   (env, [], (Prims.parse_int "0")) in
               (match uu____8310 with
                | (rec_env,memos,uu____8432) ->
                    let uu____8447 =
                      FStar_List.map2
                        (fun lb  ->
                           fun memo  ->
                             FStar_ST.write memo
                               (Some
                                  (rec_env, (lb.FStar_Syntax_Syntax.lbdef))))
                        (snd lbs) memos in
                    let body_env =
                      FStar_List.fold_right
                        (fun lb  ->
                           fun env1  ->
                             let uu____8489 =
                               let uu____8490 =
                                 let uu____8500 = FStar_Util.mk_ref None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____8500, false) in
                               Clos uu____8490 in
                             uu____8489 :: env1) (snd lbs) env in
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
                             FStar_Syntax_Syntax.tk = uu____8538;
                             FStar_Syntax_Syntax.pos = uu____8539;
                             FStar_Syntax_Syntax.vars = uu____8540;_},uu____8541,uu____8542))::uu____8543
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____8549 -> false in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____8556 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____8556
                        then
                          let uu___174_8557 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___174_8557.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps = (uu___174_8557.primitive_steps)
                          }
                        else
                          (let uu___175_8559 = cfg in
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___175_8559.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta];
                             primitive_steps =
                               (uu___175_8559.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____8561 =
                         let uu____8562 = FStar_Syntax_Subst.compress head1 in
                         uu____8562.FStar_Syntax_Syntax.n in
                       match uu____8561 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____8576 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8576 with
                            | (uu____8577,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____8581 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____8588 =
                                         let uu____8589 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____8589.FStar_Syntax_Syntax.n in
                                       match uu____8588 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____8594,uu____8595))
                                           ->
                                           let uu____8604 =
                                             let uu____8605 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____8605.FStar_Syntax_Syntax.n in
                                           (match uu____8604 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____8610,msrc,uu____8612))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____8621 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                Some uu____8621
                                            | uu____8622 -> None)
                                       | uu____8623 -> None in
                                     let uu____8624 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____8624 with
                                      | Some e ->
                                          let lb1 =
                                            let uu___176_8628 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___176_8628.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___176_8628.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___176_8628.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Syntax_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____8629 =
                                            FStar_List.tl stack1 in
                                          let uu____8630 =
                                            let uu____8631 =
                                              let uu____8634 =
                                                let uu____8635 =
                                                  let uu____8643 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____8643) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____8635 in
                                              FStar_Syntax_Syntax.mk
                                                uu____8634 in
                                            uu____8631 None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____8629 uu____8630
                                      | None  ->
                                          let uu____8660 =
                                            let uu____8661 = is_return body in
                                            match uu____8661 with
                                            | Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____8664;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____8665;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____8666;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____8671 -> false in
                                          if uu____8660
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
                                               let uu____8691 =
                                                 let uu____8694 =
                                                   let uu____8695 =
                                                     let uu____8710 =
                                                       let uu____8712 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____8712] in
                                                     (uu____8710, body1,
                                                       (Some
                                                          (FStar_Util.Inr
                                                             (m1, [])))) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____8695 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8694 in
                                               uu____8691 None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____8745 =
                                                 let uu____8746 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____8746.FStar_Syntax_Syntax.n in
                                               match uu____8745 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____8752::uu____8753::[])
                                                   ->
                                                   let uu____8759 =
                                                     let uu____8762 =
                                                       let uu____8763 =
                                                         let uu____8768 =
                                                           let uu____8770 =
                                                             let uu____8771 =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____8771 in
                                                           let uu____8772 =
                                                             let uu____8774 =
                                                               let uu____8775
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____8775 in
                                                             [uu____8774] in
                                                           uu____8770 ::
                                                             uu____8772 in
                                                         (bind1, uu____8768) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____8763 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8762 in
                                                   uu____8759 None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____8787 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____8793 =
                                                 let uu____8796 =
                                                   let uu____8797 =
                                                     let uu____8807 =
                                                       let uu____8809 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____8810 =
                                                         let uu____8812 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____8813 =
                                                           let uu____8815 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____8816 =
                                                             let uu____8818 =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____8819 =
                                                               let uu____8821
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____8822
                                                                 =
                                                                 let uu____8824
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____8824] in
                                                               uu____8821 ::
                                                                 uu____8822 in
                                                             uu____8818 ::
                                                               uu____8819 in
                                                           uu____8815 ::
                                                             uu____8816 in
                                                         uu____8812 ::
                                                           uu____8813 in
                                                       uu____8809 ::
                                                         uu____8810 in
                                                     (bind_inst, uu____8807) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____8797 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8796 in
                                               uu____8793 None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____8836 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____8836 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____8854 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8854 with
                            | (uu____8855,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____8878 =
                                        let uu____8879 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____8879.FStar_Syntax_Syntax.n in
                                      match uu____8878 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____8885) -> t4
                                      | uu____8890 -> head2 in
                                    let uu____8891 =
                                      let uu____8892 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____8892.FStar_Syntax_Syntax.n in
                                    match uu____8891 with
                                    | FStar_Syntax_Syntax.Tm_fvar x -> Some x
                                    | uu____8897 -> None in
                                  let uu____8898 = maybe_extract_fv head2 in
                                  match uu____8898 with
                                  | Some x when
                                      let uu____8904 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____8904
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____8908 =
                                          maybe_extract_fv head3 in
                                        match uu____8908 with
                                        | Some uu____8911 -> Some true
                                        | uu____8912 -> Some false in
                                      (head3, action_unfolded)
                                  | uu____8915 -> (head2, None) in
                                ((let is_arg_impure uu____8926 =
                                    match uu____8926 with
                                    | (e,q) ->
                                        let uu____8931 =
                                          let uu____8932 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____8932.FStar_Syntax_Syntax.n in
                                        (match uu____8931 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____8947 -> false) in
                                  let uu____8948 =
                                    let uu____8949 =
                                      let uu____8953 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____8953 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____8949 in
                                  if uu____8948
                                  then
                                    let uu____8956 =
                                      let uu____8957 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____8957 in
                                    failwith uu____8956
                                  else ());
                                 (let uu____8959 =
                                    maybe_unfold_action head_app in
                                  match uu____8959 with
                                  | (head_app1,found_action) ->
                                      let mk1 tm =
                                        FStar_Syntax_Syntax.mk tm None
                                          t2.FStar_Syntax_Syntax.pos in
                                      let body =
                                        mk1
                                          (FStar_Syntax_Syntax.Tm_app
                                             (head_app1, args)) in
                                      let body1 =
                                        match found_action with
                                        | None  ->
                                            FStar_Syntax_Util.mk_reify body
                                        | Some (false ) ->
                                            mk1
                                              (FStar_Syntax_Syntax.Tm_meta
                                                 (body,
                                                   (FStar_Syntax_Syntax.Meta_monadic
                                                      (m1, t2))))
                                        | Some (true ) -> body in
                                      let uu____8994 = FStar_List.tl stack1 in
                                      norm cfg env uu____8994 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____9008 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____9008 in
                           let uu____9009 = FStar_List.tl stack1 in
                           norm cfg env uu____9009 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____9092  ->
                                     match uu____9092 with
                                     | (pat,wopt,tm) ->
                                         let uu____9130 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____9130))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____9156 = FStar_List.tl stack1 in
                           norm cfg env uu____9156 tm
                       | uu____9157 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.tk = uu____9166;
                             FStar_Syntax_Syntax.pos = uu____9167;
                             FStar_Syntax_Syntax.vars = uu____9168;_},uu____9169,uu____9170))::uu____9171
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____9177 -> false in
                    if should_reify
                    then
                      let uu____9178 = FStar_List.tl stack1 in
                      let uu____9179 =
                        let uu____9180 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____9180 in
                      norm cfg env uu____9178 uu____9179
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____9183 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____9183
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___177_9189 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___177_9189.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___177_9189.primitive_steps)
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
                | uu____9191 ->
                    (match stack1 with
                     | uu____9192::uu____9193 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____9197)
                              -> norm cfg env ((Meta (m, r)) :: stack1) head1
                          | FStar_Syntax_Syntax.Meta_pattern args ->
                              let args1 = norm_pattern_args cfg env args in
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_pattern args1),
                                      (t1.FStar_Syntax_Syntax.pos))) ::
                                stack1) head1
                          | uu____9212 -> norm cfg env stack1 head1)
                     | [] ->
                         let head2 = norm cfg env [] head1 in
                         let m1 =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               let uu____9222 =
                                 norm_pattern_args cfg env args in
                               FStar_Syntax_Syntax.Meta_pattern uu____9222
                           | uu____9229 -> m in
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
              let uu____9241 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____9241 with
              | (uu____9242,return_repr) ->
                  let return_inst =
                    let uu____9249 =
                      let uu____9250 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____9250.FStar_Syntax_Syntax.n in
                    match uu____9249 with
                    | FStar_Syntax_Syntax.Tm_uinst (return_tm,uu____9256::[])
                        ->
                        let uu____9262 =
                          let uu____9265 =
                            let uu____9266 =
                              let uu____9271 =
                                let uu____9273 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____9273] in
                              (return_tm, uu____9271) in
                            FStar_Syntax_Syntax.Tm_uinst uu____9266 in
                          FStar_Syntax_Syntax.mk uu____9265 in
                        uu____9262 None e.FStar_Syntax_Syntax.pos
                    | uu____9285 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____9288 =
                    let uu____9291 =
                      let uu____9292 =
                        let uu____9302 =
                          let uu____9304 = FStar_Syntax_Syntax.as_arg t in
                          let uu____9305 =
                            let uu____9307 = FStar_Syntax_Syntax.as_arg e in
                            [uu____9307] in
                          uu____9304 :: uu____9305 in
                        (return_inst, uu____9302) in
                      FStar_Syntax_Syntax.Tm_app uu____9292 in
                    FStar_Syntax_Syntax.mk uu____9291 in
                  uu____9288 None e.FStar_Syntax_Syntax.pos
            else
              (let uu____9320 = FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____9320 with
               | None  ->
                   let uu____9322 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____9322
               | Some
                   { FStar_TypeChecker_Env.msource = uu____9323;
                     FStar_TypeChecker_Env.mtarget = uu____9324;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____9325;
                         FStar_TypeChecker_Env.mlift_term = None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | Some
                   { FStar_TypeChecker_Env.msource = uu____9336;
                     FStar_TypeChecker_Env.mtarget = uu____9337;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____9338;
                         FStar_TypeChecker_Env.mlift_term = Some lift;_};_}
                   ->
                   let uu____9356 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____9356)
and norm_pattern_args:
  cfg ->
    env ->
      ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax* FStar_Syntax_Syntax.aqual) Prims.list
        Prims.list ->
        (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.aqual) Prims.list
          Prims.list
  =
  fun cfg  ->
    fun env  ->
      fun args  ->
        FStar_All.pipe_right args
          (FStar_List.map
             (FStar_List.map
                (fun uu____9386  ->
                   match uu____9386 with
                   | (a,imp) ->
                       let uu____9393 = norm cfg env [] a in
                       (uu____9393, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___178_9408 = comp1 in
            let uu____9411 =
              let uu____9412 =
                let uu____9418 = norm cfg env [] t in
                let uu____9419 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____9418, uu____9419) in
              FStar_Syntax_Syntax.Total uu____9412 in
            {
              FStar_Syntax_Syntax.n = uu____9411;
              FStar_Syntax_Syntax.tk = (uu___178_9408.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___178_9408.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___178_9408.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___179_9434 = comp1 in
            let uu____9437 =
              let uu____9438 =
                let uu____9444 = norm cfg env [] t in
                let uu____9445 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____9444, uu____9445) in
              FStar_Syntax_Syntax.GTotal uu____9438 in
            {
              FStar_Syntax_Syntax.n = uu____9437;
              FStar_Syntax_Syntax.tk = (uu___179_9434.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___179_9434.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___179_9434.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____9476  ->
                      match uu____9476 with
                      | (a,i) ->
                          let uu____9483 = norm cfg env [] a in
                          (uu____9483, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___143_9488  ->
                      match uu___143_9488 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____9492 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____9492
                      | f -> f)) in
            let uu___180_9496 = comp1 in
            let uu____9499 =
              let uu____9500 =
                let uu___181_9501 = ct in
                let uu____9502 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____9503 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____9506 = norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____9502;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___181_9501.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____9503;
                  FStar_Syntax_Syntax.effect_args = uu____9506;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____9500 in
            {
              FStar_Syntax_Syntax.n = uu____9499;
              FStar_Syntax_Syntax.tk = (uu___180_9496.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___180_9496.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___180_9496.FStar_Syntax_Syntax.vars)
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
            (let uu___182_9523 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___182_9523.tcenv);
               delta_level = (uu___182_9523.delta_level);
               primitive_steps = (uu___182_9523.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____9528 = norm1 t in
          FStar_Syntax_Util.non_informative uu____9528 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____9531 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___183_9545 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.tk = (uu___183_9545.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___183_9545.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___183_9545.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____9555 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____9555
            then
              let ct1 =
                match downgrade_ghost_effect_name
                        ct.FStar_Syntax_Syntax.effect_name
                with
                | Some pure_eff ->
                    let uu___184_9560 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___184_9560.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___184_9560.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___184_9560.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___184_9560.FStar_Syntax_Syntax.flags)
                    }
                | None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___185_9562 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___185_9562.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Syntax_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___185_9562.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___185_9562.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___185_9562.FStar_Syntax_Syntax.flags)
                    } in
              let uu___186_9563 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.tk =
                  (uu___186_9563.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___186_9563.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___186_9563.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____9569 -> c
and norm_binder:
  cfg ->
    env ->
      FStar_Syntax_Syntax.binder ->
        (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  =
  fun cfg  ->
    fun env  ->
      fun uu____9572  ->
        match uu____9572 with
        | (x,imp) ->
            let uu____9575 =
              let uu___187_9576 = x in
              let uu____9577 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___187_9576.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___187_9576.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____9577
              } in
            (uu____9575, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____9583 =
          FStar_List.fold_left
            (fun uu____9590  ->
               fun b  ->
                 match uu____9590 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____9583 with | (nbs,uu____9607) -> FStar_List.rev nbs
and norm_lcomp_opt:
  cfg ->
    env ->
      (FStar_Syntax_Syntax.lcomp,FStar_Syntax_Syntax.residual_comp)
        FStar_Util.either option ->
        (FStar_Syntax_Syntax.lcomp,FStar_Syntax_Syntax.residual_comp)
          FStar_Util.either option
  =
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | Some (FStar_Util.Inl lc) ->
            let flags = filter_out_lcomp_cflags lc in
            let uu____9624 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
            if uu____9624
            then
              let t = norm cfg env [] lc.FStar_Syntax_Syntax.res_typ in
              let uu____9629 = FStar_Syntax_Util.is_total_lcomp lc in
              (if uu____9629
               then
                 let uu____9633 =
                   let uu____9636 =
                     let uu____9637 =
                       let uu____9640 = FStar_Syntax_Syntax.mk_Total t in
                       FStar_Syntax_Util.comp_set_flags uu____9640 flags in
                     FStar_Syntax_Util.lcomp_of_comp uu____9637 in
                   FStar_Util.Inl uu____9636 in
                 Some uu____9633
               else
                 (let uu____9644 =
                    let uu____9647 =
                      let uu____9648 =
                        let uu____9651 = FStar_Syntax_Syntax.mk_GTotal t in
                        FStar_Syntax_Util.comp_set_flags uu____9651 flags in
                      FStar_Syntax_Util.lcomp_of_comp uu____9648 in
                    FStar_Util.Inl uu____9647 in
                  Some uu____9644))
            else
              Some
                (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags))
        | uu____9664 -> lopt
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
              ((let uu____9676 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____9676
                then
                  let uu____9677 = FStar_Syntax_Print.term_to_string tm in
                  let uu____9678 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2 "Normalized %s to %s\n" uu____9677
                    uu____9678
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___188_9689 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___188_9689.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____9709  ->
                    let uu____9710 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____9710);
               rebuild cfg env stack2 t)
          | (Let (env',bs,lb,r))::stack2 ->
              let body = FStar_Syntax_Subst.close bs t in
              let t1 =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_let ((false, [lb]), body)) None r in
              rebuild cfg env' stack2 t1
          | (Abs (env',bs,env'',lopt,r))::stack2 ->
              let bs1 = norm_binders cfg env' bs in
              let lopt1 = norm_lcomp_opt cfg env'' lopt in
              let uu____9747 =
                let uu___189_9748 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___189_9748.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___189_9748.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___189_9748.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____9747
          | (Arg (Univ uu____9753,uu____9754,uu____9755))::uu____9756 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____9758,uu____9759))::uu____9760 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____9772),aq,r))::stack2 ->
              (log cfg
                 (fun uu____9788  ->
                    let uu____9789 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____9789);
               if FStar_List.contains (Exclude Iota) cfg.steps
               then
                 (if FStar_List.contains WHNF cfg.steps
                  then
                    let arg = closure_as_term cfg env1 tm in
                    let t1 =
                      FStar_Syntax_Syntax.extend_app t (arg, aq) None r in
                    rebuild cfg env1 stack2 t1
                  else
                    (let stack3 = (App (t, aq, r)) :: stack2 in
                     norm cfg env1 stack3 tm))
               else
                 (let uu____9800 = FStar_ST.read m in
                  match uu____9800 with
                  | None  ->
                      if FStar_List.contains WHNF cfg.steps
                      then
                        let arg = closure_as_term cfg env1 tm in
                        let t1 =
                          FStar_Syntax_Syntax.extend_app t (arg, aq) None r in
                        rebuild cfg env1 stack2 t1
                      else
                        (let stack3 = (MemoLazy m) :: (App (t, aq, r)) ::
                           stack2 in
                         norm cfg env1 stack3 tm)
                  | Some (uu____9826,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq) None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.extend_app head1 (t, aq) None r in
              let uu____9848 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____9848
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____9855  ->
                    let uu____9856 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____9856);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____9861 =
                  log cfg
                    (fun uu____9863  ->
                       let uu____9864 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____9865 =
                         let uu____9866 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____9873  ->
                                   match uu____9873 with
                                   | (p,uu____9879,uu____9880) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____9866
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____9864 uu____9865);
                  (let whnf = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___144_9890  ->
                               match uu___144_9890 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____9891 -> false)) in
                     let steps' =
                       let uu____9894 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____9894
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___190_9897 = cfg in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___190_9897.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___190_9897.primitive_steps)
                     } in
                   let norm_or_whnf env2 t1 =
                     if whnf
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____9931 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____9947 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____9981  ->
                                   fun uu____9982  ->
                                     match (uu____9981, uu____9982) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____10047 = norm_pat env3 p1 in
                                         (match uu____10047 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____9947 with
                          | (pats1,env3) ->
                              ((let uu___191_10113 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___191_10113.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___191_10113.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___192_10127 = x in
                           let uu____10128 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___192_10127.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___192_10127.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____10128
                           } in
                         ((let uu___193_10134 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___193_10134.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___193_10134.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___194_10139 = x in
                           let uu____10140 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___194_10139.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___194_10139.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____10140
                           } in
                         ((let uu___195_10146 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___195_10146.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___195_10146.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___196_10156 = x in
                           let uu____10157 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___196_10156.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___196_10156.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____10157
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___197_10164 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.ty =
                               (uu___197_10164.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___197_10164.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf -> branches
                     | uu____10168 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____10171 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____10171 with
                                 | (p,wopt,e) ->
                                     let uu____10189 = norm_pat env1 p in
                                     (match uu____10189 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | None  -> None
                                            | Some w ->
                                                let uu____10213 =
                                                  norm_or_whnf env2 w in
                                                Some uu____10213 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____10218 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____10218) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____10228) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____10233 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____10234;
                        FStar_Syntax_Syntax.fv_delta = uu____10235;
                        FStar_Syntax_Syntax.fv_qual = Some
                          (FStar_Syntax_Syntax.Data_ctor );_}
                      -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____10239;
                        FStar_Syntax_Syntax.fv_delta = uu____10240;
                        FStar_Syntax_Syntax.fv_qual = Some
                          (FStar_Syntax_Syntax.Record_ctor uu____10241);_}
                      -> true
                  | uu____10248 -> false in
                let guard_when_clause wopt b rest =
                  match wopt with
                  | None  -> b
                  | Some w ->
                      let then_branch = b in
                      let else_branch =
                        mk (FStar_Syntax_Syntax.Tm_match (scrutinee, rest)) r in
                      FStar_Syntax_Util.if_then_else w then_branch
                        else_branch in
                let rec matches_pat scrutinee_orig p =
                  let scrutinee1 = FStar_Syntax_Util.unmeta scrutinee_orig in
                  let uu____10347 =
                    FStar_Syntax_Util.head_and_args scrutinee1 in
                  match uu____10347 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var uu____10379 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_wild uu____10381 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____10383 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee1.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____10395 ->
                                let uu____10396 =
                                  let uu____10397 = is_cons head1 in
                                  Prims.op_Negation uu____10397 in
                                FStar_Util.Inr uu____10396)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____10411 =
                             let uu____10412 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____10412.FStar_Syntax_Syntax.n in
                           (match uu____10411 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____10419 ->
                                let uu____10420 =
                                  let uu____10421 = is_cons head1 in
                                  Prims.op_Negation uu____10421 in
                                FStar_Util.Inr uu____10420))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____10455)::rest_a,(p1,uu____10458)::rest_p) ->
                      let uu____10486 = matches_pat t1 p1 in
                      (match uu____10486 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____10500 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____10571 = matches_pat scrutinee1 p1 in
                      (match uu____10571 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____10581  ->
                                 let uu____10582 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____10583 =
                                   let uu____10584 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____10584
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____10582 uu____10583);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____10593 =
                                        let uu____10594 =
                                          let uu____10604 =
                                            FStar_Util.mk_ref (Some ([], t1)) in
                                          ([], t1, uu____10604, false) in
                                        Clos uu____10594 in
                                      uu____10593 :: env2) env1 s in
                             let uu____10627 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____10627))) in
                let uu____10628 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____10628
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___145_10644  ->
                match uu___145_10644 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____10647 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____10651 -> d in
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
            let uu___198_10675 = config s e in
            {
              steps = (uu___198_10675.steps);
              tcenv = (uu___198_10675.tcenv);
              delta_level = (uu___198_10675.delta_level);
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
      fun t  -> let uu____10700 = config s e in norm_comp uu____10700 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____10709 = config [] env in norm_universe uu____10709 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun c  ->
      let uu____10718 = config [] env in ghost_to_pure_aux uu____10718 [] c
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
        let uu____10732 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____10732 in
      let uu____10733 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____10733
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | Some pure_eff ->
            let uu___199_10735 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___199_10735.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___199_10735.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____10736  ->
                    let uu____10737 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____10737))
            }
        | None  -> lc
      else lc
let term_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun env  ->
    fun t  ->
      let t1 =
        try normalize [AllowUnboundUniverses] env t
        with
        | e ->
            ((let uu____10752 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10752);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____10763 = config [AllowUnboundUniverses] env in
          norm_comp uu____10763 [] c
        with
        | e ->
            ((let uu____10767 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10767);
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
                   let uu____10807 =
                     let uu____10808 =
                       let uu____10813 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____10813) in
                     FStar_Syntax_Syntax.Tm_refine uu____10808 in
                   mk uu____10807 t01.FStar_Syntax_Syntax.pos
               | uu____10818 -> t2)
          | uu____10819 -> t2 in
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
        let uu____10848 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____10848 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____10864 ->
                 let uu____10868 = FStar_Syntax_Util.abs_formals e in
                 (match uu____10868 with
                  | (actuals,uu____10879,uu____10880) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____10906 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____10906 with
                         | (binders,args) ->
                             let uu____10916 =
                               FStar_Syntax_Syntax.mk_Tm_app e args None
                                 e.FStar_Syntax_Syntax.pos in
                             let uu____10919 =
                               let uu____10926 =
                                 FStar_All.pipe_right
                                   (FStar_Syntax_Util.lcomp_of_comp c)
                                   (fun _0_54  -> FStar_Util.Inl _0_54) in
                               FStar_All.pipe_right uu____10926
                                 (fun _0_55  -> Some _0_55) in
                             FStar_Syntax_Util.abs binders uu____10916
                               uu____10919)))
let eta_expand:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____10964 =
        let uu____10968 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
        (uu____10968, (t.FStar_Syntax_Syntax.n)) in
      match uu____10964 with
      | (Some sort,uu____10975) ->
          let uu____10977 = mk sort t.FStar_Syntax_Syntax.pos in
          eta_expand_with_type env t uu____10977
      | (uu____10978,FStar_Syntax_Syntax.Tm_name x) ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____10982 ->
          let uu____10986 = FStar_Syntax_Util.head_and_args t in
          (match uu____10986 with
           | (head1,args) ->
               let uu____11012 =
                 let uu____11013 = FStar_Syntax_Subst.compress head1 in
                 uu____11013.FStar_Syntax_Syntax.n in
               (match uu____11012 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____11016,thead) ->
                    let uu____11030 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____11030 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____11065 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___204_11069 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___204_11069.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___204_11069.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___204_11069.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___204_11069.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___204_11069.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___204_11069.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ = None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___204_11069.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___204_11069.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___204_11069.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___204_11069.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___204_11069.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___204_11069.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___204_11069.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___204_11069.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___204_11069.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___204_11069.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___204_11069.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___204_11069.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___204_11069.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___204_11069.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___204_11069.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___204_11069.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___204_11069.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___204_11069.FStar_TypeChecker_Env.is_native_tactic)
                                 }) t in
                            match uu____11065 with
                            | (uu____11070,ty,uu____11072) ->
                                eta_expand_with_type env t ty))
                | uu____11073 ->
                    let uu____11074 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___205_11078 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___205_11078.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___205_11078.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___205_11078.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___205_11078.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___205_11078.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___205_11078.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ = None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___205_11078.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___205_11078.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___205_11078.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___205_11078.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___205_11078.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___205_11078.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___205_11078.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___205_11078.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___205_11078.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___205_11078.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___205_11078.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___205_11078.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___205_11078.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___205_11078.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___205_11078.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___205_11078.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___205_11078.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___205_11078.FStar_TypeChecker_Env.is_native_tactic)
                         }) t in
                    (match uu____11074 with
                     | (uu____11079,ty,uu____11081) ->
                         eta_expand_with_type env t ty)))