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
  fun projectee  -> match projectee with | Beta  -> true | uu____10 -> false
let uu___is_Iota: step -> Prims.bool =
  fun projectee  -> match projectee with | Iota  -> true | uu____14 -> false
let uu___is_Zeta: step -> Prims.bool =
  fun projectee  -> match projectee with | Zeta  -> true | uu____18 -> false
let uu___is_Exclude: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____23 -> false
let __proj__Exclude__item___0: step -> step =
  fun projectee  -> match projectee with | Exclude _0 -> _0
let uu___is_WHNF: step -> Prims.bool =
  fun projectee  -> match projectee with | WHNF  -> true | uu____34 -> false
let uu___is_Primops: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____38 -> false
let uu___is_Eager_unfolding: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____42 -> false
let uu___is_Inlining: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____46 -> false
let uu___is_NoDeltaSteps: step -> Prims.bool =
  fun projectee  ->
    match projectee with | NoDeltaSteps  -> true | uu____50 -> false
let uu___is_UnfoldUntil: step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____55 -> false
let __proj__UnfoldUntil__item___0: step -> FStar_Syntax_Syntax.delta_depth =
  fun projectee  -> match projectee with | UnfoldUntil _0 -> _0
let uu___is_PureSubtermsWithinComputations: step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____66 -> false
let uu___is_Simplify: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____70 -> false
let uu___is_EraseUniverses: step -> Prims.bool =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____74 -> false
let uu___is_AllowUnboundUniverses: step -> Prims.bool =
  fun projectee  ->
    match projectee with | AllowUnboundUniverses  -> true | uu____78 -> false
let uu___is_Reify: step -> Prims.bool =
  fun projectee  -> match projectee with | Reify  -> true | uu____82 -> false
let uu___is_CompressUvars: step -> Prims.bool =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____86 -> false
let uu___is_NoFullNorm: step -> Prims.bool =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____90 -> false
type steps = step Prims.list
type closure =
  | Clos of (closure Prims.list* FStar_Syntax_Syntax.term* (closure
  Prims.list* FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo*
  Prims.bool)
  | Univ of FStar_Syntax_Syntax.universe
  | Dummy
let uu___is_Clos: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Clos _0 -> true | uu____120 -> false
let __proj__Clos__item___0:
  closure ->
    (closure Prims.list* FStar_Syntax_Syntax.term* (closure Prims.list*
      FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo* Prims.bool)
  = fun projectee  -> match projectee with | Clos _0 -> _0
let uu___is_Univ: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____159 -> false
let __proj__Univ__item___0: closure -> FStar_Syntax_Syntax.universe =
  fun projectee  -> match projectee with | Univ _0 -> _0
let uu___is_Dummy: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____170 -> false
type env = closure Prims.list
let closure_to_string: closure -> Prims.string =
  fun uu___123_174  ->
    match uu___123_174 with
    | Clos (uu____175,t,uu____177,uu____178) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____189 -> "Univ"
    | Dummy  -> "dummy"
type cfg =
  {
  steps: steps;
  tcenv: FStar_TypeChecker_Env.env;
  delta_level: FStar_TypeChecker_Env.delta_level Prims.list;}
type branches =
  (FStar_Syntax_Syntax.pat* FStar_Syntax_Syntax.term Prims.option*
    FStar_Syntax_Syntax.term) Prims.list
type subst_t = FStar_Syntax_Syntax.subst_elt Prims.list
type stack_elt =
  | Arg of (closure* FStar_Syntax_Syntax.aqual* FStar_Range.range)
  | UnivArgs of (FStar_Syntax_Syntax.universe Prims.list* FStar_Range.range)
  | MemoLazy of (env* FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo
  | Match of (env* branches* FStar_Range.range)
  | Abs of (env* FStar_Syntax_Syntax.binders* env*
  (FStar_Syntax_Syntax.lcomp,FStar_Syntax_Syntax.residual_comp)
  FStar_Util.either Prims.option* FStar_Range.range)
  | App of (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.aqual*
  FStar_Range.range)
  | Meta of (FStar_Syntax_Syntax.metadata* FStar_Range.range)
  | Let of (env* FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.letbinding*
  FStar_Range.range)
  | Steps of (steps* FStar_TypeChecker_Env.delta_level Prims.list)
  | Debug of FStar_Syntax_Syntax.term
let uu___is_Arg: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Arg _0 -> true | uu____290 -> false
let __proj__Arg__item___0:
  stack_elt -> (closure* FStar_Syntax_Syntax.aqual* FStar_Range.range) =
  fun projectee  -> match projectee with | Arg _0 -> _0
let uu___is_UnivArgs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____314 -> false
let __proj__UnivArgs__item___0:
  stack_elt -> (FStar_Syntax_Syntax.universe Prims.list* FStar_Range.range) =
  fun projectee  -> match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____338 -> false
let __proj__MemoLazy__item___0:
  stack_elt -> (env* FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo =
  fun projectee  -> match projectee with | MemoLazy _0 -> _0
let uu___is_Match: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____365 -> false
let __proj__Match__item___0: stack_elt -> (env* branches* FStar_Range.range)
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Abs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____394 -> false
let __proj__Abs__item___0:
  stack_elt ->
    (env* FStar_Syntax_Syntax.binders* env*
      (FStar_Syntax_Syntax.lcomp,FStar_Syntax_Syntax.residual_comp)
      FStar_Util.either Prims.option* FStar_Range.range)
  = fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____433 -> false
let __proj__App__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.aqual* FStar_Range.range)
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Meta: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____456 -> false
let __proj__Meta__item___0:
  stack_elt -> (FStar_Syntax_Syntax.metadata* FStar_Range.range) =
  fun projectee  -> match projectee with | Meta _0 -> _0
let uu___is_Let: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____478 -> false
let __proj__Let__item___0:
  stack_elt ->
    (env* FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.letbinding*
      FStar_Range.range)
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Steps: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Steps _0 -> true | uu____505 -> false
let __proj__Steps__item___0:
  stack_elt -> (steps* FStar_TypeChecker_Env.delta_level Prims.list) =
  fun projectee  -> match projectee with | Steps _0 -> _0
let uu___is_Debug: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____526 -> false
let __proj__Debug__item___0: stack_elt -> FStar_Syntax_Syntax.term =
  fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list
let mk t r = FStar_Syntax_Syntax.mk t None r
let set_memo r t =
  let uu____574 = FStar_ST.read r in
  match uu____574 with
  | Some uu____579 -> failwith "Unexpected set_memo: thunk already evaluated"
  | None  -> FStar_ST.write r (Some t)
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____588 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____588 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___124_593  ->
    match uu___124_593 with
    | Arg (c,uu____595,uu____596) ->
        let uu____597 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____597
    | MemoLazy uu____598 -> "MemoLazy"
    | Abs (uu____602,bs,uu____604,uu____605,uu____606) ->
        let uu____613 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____613
    | UnivArgs uu____618 -> "UnivArgs"
    | Match uu____622 -> "Match"
    | App (t,uu____627,uu____628) ->
        let uu____629 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____629
    | Meta (m,uu____631) -> "Meta"
    | Let uu____632 -> "Let"
    | Steps (s,uu____638) -> "Steps"
    | Debug t ->
        let uu____642 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____642
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____648 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____648 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____662 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____662 then f () else ()
let is_empty uu___125_671 =
  match uu___125_671 with | [] -> true | uu____673 -> false
let lookup_bvar env x =
  try FStar_List.nth env x.FStar_Syntax_Syntax.index
  with
  | uu____691 ->
      let uu____692 =
        let uu____693 = FStar_Syntax_Print.db_to_string x in
        FStar_Util.format1 "Failed to find %s\n" uu____693 in
      failwith uu____692
let downgrade_ghost_effect_name:
  FStar_Ident.lident -> FStar_Ident.lident Prims.option =
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
          let uu____724 =
            FStar_List.fold_left
              (fun uu____733  ->
                 fun u1  ->
                   match uu____733 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____748 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____748 with
                        | (k_u,n1) ->
                            let uu____757 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____757
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____724 with
          | (uu____767,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____783 = FStar_List.nth env x in
                 match uu____783 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____786 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____790 ->
                   let uu____791 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____791
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_zero 
            |FStar_Syntax_Syntax.U_unif _
             |FStar_Syntax_Syntax.U_name _|FStar_Syntax_Syntax.U_unknown  ->
              [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____801 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____801 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____812 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____812 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____817 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____820 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____820 with
                                  | (uu____823,m) -> n1 <= m)) in
                        if uu____817 then rest1 else us1
                    | uu____827 -> us1)
               | uu____830 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____833 = aux u3 in
              FStar_List.map (fun _0_29  -> FStar_Syntax_Syntax.U_succ _0_29)
                uu____833 in
        let uu____835 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____835
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____837 = aux u in
           match uu____837 with
           | []|(FStar_Syntax_Syntax.U_zero )::[] ->
               FStar_Syntax_Syntax.U_zero
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
          (fun uu____934  ->
             let uu____935 = FStar_Syntax_Print.tag_of_term t in
             let uu____936 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____935
               uu____936);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____937 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____940 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown 
                |FStar_Syntax_Syntax.Tm_constant _
                 |FStar_Syntax_Syntax.Tm_name _|FStar_Syntax_Syntax.Tm_fvar _
                  -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____964 -> t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____974 =
                    let uu____975 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____975 in
                  mk uu____974 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t2,us) ->
                  let uu____982 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t2 uu____982
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____984 = lookup_bvar env x in
                  (match uu____984 with
                   | Univ uu____985 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____989) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____1057 = closures_as_binders_delayed cfg env bs in
                  (match uu____1057 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____1077 =
                         let uu____1078 =
                           let uu____1093 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____1093) in
                         FStar_Syntax_Syntax.Tm_abs uu____1078 in
                       mk uu____1077 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____1123 = closures_as_binders_delayed cfg env bs in
                  (match uu____1123 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____1154 =
                    let uu____1161 =
                      let uu____1165 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____1165] in
                    closures_as_binders_delayed cfg env uu____1161 in
                  (match uu____1154 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____1179 =
                         let uu____1180 =
                           let uu____1185 =
                             let uu____1186 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____1186 Prims.fst in
                           (uu____1185, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____1180 in
                       mk uu____1179 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,FStar_Util.Inl t2,lopt)
                  ->
                  let uu____1216 =
                    let uu____1217 =
                      let uu____1230 = closure_as_term_delayed cfg env t11 in
                      let uu____1233 =
                        let uu____1240 = closure_as_term_delayed cfg env t2 in
                        FStar_All.pipe_left
                          (fun _0_30  -> FStar_Util.Inl _0_30) uu____1240 in
                      (uu____1230, uu____1233, lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____1217 in
                  mk uu____1216 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_ascribed (t11,FStar_Util.Inr c,lopt)
                  ->
                  let uu____1285 =
                    let uu____1286 =
                      let uu____1299 = closure_as_term_delayed cfg env t11 in
                      let uu____1302 =
                        let uu____1309 = close_comp cfg env c in
                        FStar_All.pipe_left
                          (fun _0_31  -> FStar_Util.Inr _0_31) uu____1309 in
                      (uu____1299, uu____1302, lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____1286 in
                  mk uu____1285 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____1345 =
                    let uu____1346 =
                      let uu____1351 = closure_as_term_delayed cfg env t' in
                      let uu____1354 =
                        let uu____1355 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____1355 in
                      (uu____1351, uu____1354) in
                    FStar_Syntax_Syntax.Tm_meta uu____1346 in
                  mk uu____1345 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____1397 =
                    let uu____1398 =
                      let uu____1403 = closure_as_term_delayed cfg env t' in
                      let uu____1406 =
                        let uu____1407 =
                          let uu____1412 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____1412) in
                        FStar_Syntax_Syntax.Meta_monadic uu____1407 in
                      (uu____1403, uu____1406) in
                    FStar_Syntax_Syntax.Tm_meta uu____1398 in
                  mk uu____1397 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____1431 =
                    let uu____1432 =
                      let uu____1437 = closure_as_term_delayed cfg env t' in
                      let uu____1440 =
                        let uu____1441 =
                          let uu____1447 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____1447) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____1441 in
                      (uu____1437, uu____1440) in
                    FStar_Syntax_Syntax.Tm_meta uu____1432 in
                  mk uu____1431 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____1460 =
                    let uu____1461 =
                      let uu____1466 = closure_as_term_delayed cfg env t' in
                      (uu____1466, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____1461 in
                  mk uu____1460 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____1487  -> Dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let body1 =
                    match lb.FStar_Syntax_Syntax.lbname with
                    | FStar_Util.Inr uu____1498 -> body
                    | FStar_Util.Inl uu____1499 ->
                        closure_as_term cfg (Dummy :: env0) body in
                  let lb1 =
                    let uu___137_1501 = lb in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___137_1501.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___137_1501.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = typ;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___137_1501.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = def
                    } in
                  mk (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((uu____1508,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____1532  -> fun env2  -> Dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____1537 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____1537
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____1541  -> fun env2  -> Dummy :: env2) lbs
                          env_univs in
                    let uu___138_1544 = lb in
                    let uu____1545 =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let uu____1548 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___138_1544.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___138_1544.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = uu____1545;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___138_1544.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____1548
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____1559  -> fun env1  -> Dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____1614 =
                    match uu____1614 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____1660 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_disj [] ->
                              failwith "Impossible"
                          | FStar_Syntax_Syntax.Pat_disj (hd1::tl1) ->
                              let uu____1680 = norm_pat env2 hd1 in
                              (match uu____1680 with
                               | (hd2,env') ->
                                   let tl2 =
                                     FStar_All.pipe_right tl1
                                       (FStar_List.map
                                          (fun p1  ->
                                             let uu____1716 =
                                               norm_pat env2 p1 in
                                             Prims.fst uu____1716)) in
                                   ((let uu___139_1728 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_disj (hd2
                                            :: tl2));
                                       FStar_Syntax_Syntax.ty =
                                         (uu___139_1728.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___139_1728.FStar_Syntax_Syntax.p)
                                     }), env'))
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____1745 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____1779  ->
                                        fun uu____1780  ->
                                          match (uu____1779, uu____1780) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____1845 =
                                                norm_pat env3 p1 in
                                              (match uu____1845 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____1745 with
                               | (pats1,env3) ->
                                   ((let uu___140_1911 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.ty =
                                         (uu___140_1911.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___140_1911.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___141_1925 = x in
                                let uu____1926 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___141_1925.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___141_1925.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1926
                                } in
                              ((let uu___142_1932 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___142_1932.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___142_1932.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___143_1937 = x in
                                let uu____1938 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___143_1937.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___143_1937.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1938
                                } in
                              ((let uu___144_1944 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___144_1944.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___144_1944.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___145_1954 = x in
                                let uu____1955 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___145_1954.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___145_1954.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1955
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___146_1962 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___146_1962.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___146_1962.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____1965 = norm_pat env1 pat in
                        (match uu____1965 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | None  -> None
                               | Some w ->
                                   let uu____1989 =
                                     closure_as_term cfg env2 w in
                                   Some uu____1989 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____1994 =
                    let uu____1995 =
                      let uu____2011 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____2011) in
                    FStar_Syntax_Syntax.Tm_match uu____1995 in
                  mk uu____1994 t1.FStar_Syntax_Syntax.pos))
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
        | uu____2064 -> closure_as_term cfg env t
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
        | uu____2080 ->
            FStar_List.map
              (fun uu____2090  ->
                 match uu____2090 with
                 | (x,imp) ->
                     let uu____2105 = closure_as_term_delayed cfg env x in
                     (uu____2105, imp)) args
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
        let uu____2117 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____2141  ->
                  fun uu____2142  ->
                    match (uu____2141, uu____2142) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___147_2186 = b in
                          let uu____2187 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___147_2186.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___147_2186.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____2187
                          } in
                        let env2 = Dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____2117 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____2234 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____2246 = closure_as_term_delayed cfg env t in
                 let uu____2247 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____2246 uu____2247
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____2257 = closure_as_term_delayed cfg env t in
                 let uu____2258 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____2257 uu____2258
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
                        (fun uu___126_2274  ->
                           match uu___126_2274 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____2278 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____2278
                           | f -> f)) in
                 let uu____2282 =
                   let uu___148_2283 = c1 in
                   let uu____2284 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____2284;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___148_2283.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____2282)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.cflags Prims.list =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_List.filter
         (fun uu___127_2288  ->
            match uu___127_2288 with
            | FStar_Syntax_Syntax.DECREASES uu____2289 -> false
            | uu____2292 -> true))
and close_lcomp_opt:
  cfg ->
    closure Prims.list ->
      (FStar_Syntax_Syntax.lcomp,(FStar_Ident.lident*
                                   FStar_Syntax_Syntax.cflags Prims.list))
        FStar_Util.either Prims.option ->
        (FStar_Syntax_Syntax.lcomp,(FStar_Ident.lident*
                                     FStar_Syntax_Syntax.cflags Prims.list))
          FStar_Util.either Prims.option
  =
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | Some (FStar_Util.Inl lc) ->
            let flags = filter_out_lcomp_cflags lc in
            let uu____2320 = FStar_Syntax_Util.is_total_lcomp lc in
            if uu____2320
            then
              Some
                (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, flags))
            else
              (let uu____2337 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
               if uu____2337
               then
                 Some
                   (FStar_Util.Inr
                      (FStar_Syntax_Const.effect_GTot_lid, flags))
               else
                 Some
                   (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags)))
        | uu____2363 -> lopt
let arith_ops:
  (FStar_Ident.lident* (Prims.int -> Prims.int -> FStar_Const.sconst))
    Prims.list
  =
  let int_as_const i =
    let uu____2381 =
      let uu____2387 = FStar_Util.string_of_int i in (uu____2387, None) in
    FStar_Const.Const_int uu____2381 in
  let bool_as_const b = FStar_Const.Const_bool b in
  let uu____2397 =
    let uu____2405 =
      FStar_List.map
        (fun m  ->
           let uu____2422 =
             let uu____2429 = FStar_Syntax_Const.p2l ["FStar"; m; "add"] in
             (uu____2429, (fun x  -> fun y  -> int_as_const (x + y))) in
           let uu____2436 =
             let uu____2444 =
               let uu____2451 = FStar_Syntax_Const.p2l ["FStar"; m; "sub"] in
               (uu____2451, (fun x  -> fun y  -> int_as_const (x - y))) in
             let uu____2458 =
               let uu____2466 =
                 let uu____2473 = FStar_Syntax_Const.p2l ["FStar"; m; "mul"] in
                 (uu____2473, (fun x  -> fun y  -> int_as_const (x * y))) in
               [uu____2466] in
             uu____2444 :: uu____2458 in
           uu____2422 :: uu____2436)
        ["Int8";
        "UInt8";
        "Int16";
        "UInt16";
        "Int32";
        "UInt32";
        "Int64";
        "UInt64";
        "UInt128"] in
    FStar_List.flatten uu____2405 in
  FStar_List.append
    [(FStar_Syntax_Const.op_Addition,
       ((fun x  -> fun y  -> int_as_const (x + y))));
    (FStar_Syntax_Const.op_Subtraction,
      ((fun x  -> fun y  -> int_as_const (x - y))));
    (FStar_Syntax_Const.op_Multiply,
      ((fun x  -> fun y  -> int_as_const (x * y))));
    (FStar_Syntax_Const.op_Division,
      ((fun x  -> fun y  -> int_as_const (x / y))));
    (FStar_Syntax_Const.op_LT, ((fun x  -> fun y  -> bool_as_const (x < y))));
    (FStar_Syntax_Const.op_LTE,
      ((fun x  -> fun y  -> bool_as_const (x <= y))));
    (FStar_Syntax_Const.op_GT, ((fun x  -> fun y  -> bool_as_const (x > y))));
    (FStar_Syntax_Const.op_GTE,
      ((fun x  -> fun y  -> bool_as_const (x >= y))));
    (FStar_Syntax_Const.op_Modulus,
      ((fun x  -> fun y  -> int_as_const (x mod y))))] uu____2397
let un_ops:
  (FStar_Ident.lident*
    (Prims.string ->
       (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
         FStar_Syntax_Syntax.syntax))
    Prims.list
  =
  let mk1 x = mk x FStar_Range.dummyRange in
  let name x =
    let uu____2668 =
      let uu____2669 =
        let uu____2670 = FStar_Syntax_Const.p2l x in
        FStar_Syntax_Syntax.lid_as_fv uu____2670
          FStar_Syntax_Syntax.Delta_constant None in
      FStar_Syntax_Syntax.Tm_fvar uu____2669 in
    mk1 uu____2668 in
  let ctor x =
    let uu____2679 =
      let uu____2680 =
        let uu____2681 = FStar_Syntax_Const.p2l x in
        FStar_Syntax_Syntax.lid_as_fv uu____2681
          FStar_Syntax_Syntax.Delta_constant
          (Some FStar_Syntax_Syntax.Data_ctor) in
      FStar_Syntax_Syntax.Tm_fvar uu____2680 in
    mk1 uu____2679 in
  let uu____2682 =
    let uu____2689 =
      FStar_Syntax_Const.p2l ["FStar"; "String"; "list_of_string"] in
    (uu____2689,
      (fun s  ->
         let uu____2695 = FStar_String.list_of_string s in
         let uu____2697 =
           let uu____2700 =
             let uu____2701 =
               let uu____2711 =
                 let uu____2712 = ctor ["Prims"; "Nil"] in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____2712
                   [FStar_Syntax_Syntax.U_zero] in
               let uu____2713 =
                 let uu____2720 =
                   let uu____2726 = name ["FStar"; "Char"; "char"] in
                   (uu____2726, (Some (FStar_Syntax_Syntax.Implicit true))) in
                 [uu____2720] in
               (uu____2711, uu____2713) in
             FStar_Syntax_Syntax.Tm_app uu____2701 in
           mk1 uu____2700 in
         FStar_List.fold_right
           (fun c  ->
              fun a  ->
                let uu____2754 =
                  let uu____2755 =
                    let uu____2765 =
                      let uu____2766 = ctor ["Prims"; "Cons"] in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____2766
                        [FStar_Syntax_Syntax.U_zero] in
                    let uu____2767 =
                      let uu____2774 =
                        let uu____2780 = name ["FStar"; "Char"; "char"] in
                        (uu____2780,
                          (Some (FStar_Syntax_Syntax.Implicit true))) in
                      let uu____2786 =
                        let uu____2793 =
                          let uu____2799 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_constant
                                 (FStar_Const.Const_char c)) in
                          (uu____2799, None) in
                        [uu____2793; (a, None)] in
                      uu____2774 :: uu____2786 in
                    (uu____2765, uu____2767) in
                  FStar_Syntax_Syntax.Tm_app uu____2755 in
                mk1 uu____2754) uu____2695 uu____2697)) in
  [uu____2682]
let reduce_equality:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun tm  ->
    let is_decidable_equality t =
      let uu____2859 =
        let uu____2860 = FStar_Syntax_Util.un_uinst t in
        uu____2860.FStar_Syntax_Syntax.n in
      match uu____2859 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Eq
      | uu____2864 -> false in
    let is_propositional_equality t =
      let uu____2869 =
        let uu____2870 = FStar_Syntax_Util.un_uinst t in
        uu____2870.FStar_Syntax_Syntax.n in
      match uu____2869 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.eq2_lid
      | uu____2874 -> false in
    match tm.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_app
        (op_eq_inst,(_typ,uu____2879)::(a1,uu____2881)::(a2,uu____2883)::[])
        when is_decidable_equality op_eq_inst ->
        let tt =
          let uu____2924 = FStar_Syntax_Util.eq_tm a1 a2 in
          match uu____2924 with
          | FStar_Syntax_Util.Equal  ->
              mk
                (FStar_Syntax_Syntax.Tm_constant
                   (FStar_Const.Const_bool true)) tm.FStar_Syntax_Syntax.pos
          | FStar_Syntax_Util.NotEqual  ->
              mk
                (FStar_Syntax_Syntax.Tm_constant
                   (FStar_Const.Const_bool false)) tm.FStar_Syntax_Syntax.pos
          | uu____2927 -> tm in
        tt
    | FStar_Syntax_Syntax.Tm_app (eq2_inst,_::(a1,_)::(a2,_)::[])
      |FStar_Syntax_Syntax.Tm_app (eq2_inst,(a1,_)::(a2,_)::[]) when
        is_propositional_equality eq2_inst ->
        let tt =
          let uu____2999 = FStar_Syntax_Util.eq_tm a1 a2 in
          match uu____2999 with
          | FStar_Syntax_Util.Equal  -> FStar_Syntax_Util.t_true
          | FStar_Syntax_Util.NotEqual  -> FStar_Syntax_Util.t_false
          | uu____3000 -> tm in
        tt
    | uu____3001 -> tm
let find_fv fv ops =
  match fv.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_fvar fv1 ->
      FStar_List.tryFind
        (fun uu____3026  ->
           match uu____3026 with
           | (l,uu____3030) -> FStar_Syntax_Syntax.fv_eq_lid fv1 l) ops
  | uu____3031 -> None
let reduce_primops:
  step Prims.list ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun steps  ->
    fun tm  ->
      let uu____3048 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops steps) in
      if uu____3048
      then tm
      else
        (match tm.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_app
             (fv,(a1,uu____3056)::(a2,uu____3058)::[]) ->
             let uu____3088 = find_fv fv arith_ops in
             (match uu____3088 with
              | None  -> tm
              | Some (uu____3108,op) ->
                  let norm i j =
                    let c =
                      let uu____3134 = FStar_Util.int_of_string i in
                      let uu____3135 = FStar_Util.int_of_string j in
                      op uu____3134 uu____3135 in
                    mk (FStar_Syntax_Syntax.Tm_constant c)
                      tm.FStar_Syntax_Syntax.pos in
                  let uu____3136 =
                    let uu____3139 =
                      let uu____3140 = FStar_Syntax_Subst.compress a1 in
                      uu____3140.FStar_Syntax_Syntax.n in
                    let uu____3143 =
                      let uu____3144 = FStar_Syntax_Subst.compress a2 in
                      uu____3144.FStar_Syntax_Syntax.n in
                    (uu____3139, uu____3143) in
                  (match uu____3136 with
                   | (FStar_Syntax_Syntax.Tm_app
                      (head1,(arg1,uu____3151)::[]),FStar_Syntax_Syntax.Tm_app
                      (head2,(arg2,uu____3154)::[])) ->
                       let uu____3197 =
                         let uu____3202 =
                           let uu____3203 = FStar_Syntax_Subst.compress head1 in
                           uu____3203.FStar_Syntax_Syntax.n in
                         let uu____3206 =
                           let uu____3207 = FStar_Syntax_Subst.compress head2 in
                           uu____3207.FStar_Syntax_Syntax.n in
                         let uu____3210 =
                           let uu____3211 = FStar_Syntax_Subst.compress arg1 in
                           uu____3211.FStar_Syntax_Syntax.n in
                         let uu____3214 =
                           let uu____3215 = FStar_Syntax_Subst.compress arg2 in
                           uu____3215.FStar_Syntax_Syntax.n in
                         (uu____3202, uu____3206, uu____3210, uu____3214) in
                       (match uu____3197 with
                        | (FStar_Syntax_Syntax.Tm_fvar
                           fv1,FStar_Syntax_Syntax.Tm_fvar
                           fv2,FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_int
                           (i,None )),FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_int (j,None ))) when
                            (FStar_Util.ends_with
                               (FStar_Ident.text_of_lid
                                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                               "int_to_t")
                              &&
                              (FStar_Util.ends_with
                                 (FStar_Ident.text_of_lid
                                    (fv2.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                 "int_to_t")
                            ->
                            let uu____3242 =
                              mk (FStar_Syntax_Syntax.Tm_fvar fv1)
                                tm.FStar_Syntax_Syntax.pos in
                            let uu____3245 =
                              let uu____3251 =
                                let uu____3257 = norm i j in
                                (uu____3257, None) in
                              [uu____3251] in
                            FStar_Syntax_Util.mk_app uu____3242 uu____3245
                        | uu____3273 -> tm)
                   | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                      (i,None )),FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_int (j,None ))) -> norm i j
                   | uu____3290 -> tm))
         | FStar_Syntax_Syntax.Tm_app (fv,(a1,uu____3295)::[]) ->
             let uu____3317 = find_fv fv un_ops in
             (match uu____3317 with
              | None  -> tm
              | Some (uu____3337,op) ->
                  let uu____3353 =
                    let uu____3354 = FStar_Syntax_Subst.compress a1 in
                    uu____3354.FStar_Syntax_Syntax.n in
                  (match uu____3353 with
                   | FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_string (b,uu____3360)) ->
                       let uu____3363 = FStar_Bytes.unicode_bytes_as_string b in
                       op uu____3363
                   | uu____3364 -> tm))
         | uu____3365 -> reduce_equality tm)
let maybe_simplify:
  step Prims.list ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun steps  ->
    fun tm  ->
      let w t =
        let uu___149_3390 = t in
        {
          FStar_Syntax_Syntax.n = (uu___149_3390.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___149_3390.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___149_3390.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid ->
            Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid ->
            Some false
        | uu____3409 -> None in
      let simplify arg = ((simp_t (Prims.fst arg)), arg) in
      let uu____3436 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps) in
      if uu____3436
      then reduce_primops steps tm
      else
        (match tm.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _;
                   FStar_Syntax_Syntax.vars = _;_},_);
              FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _;
              FStar_Syntax_Syntax.vars = _;_},args)
           |FStar_Syntax_Syntax.Tm_app
           ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
              FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _;
              FStar_Syntax_Syntax.vars = _;_},args)
             ->
             let uu____3480 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____3480
             then
               let uu____3483 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____3483 with
                | (Some (true ),_)::(_,(arg,_))::[]
                  |(_,(arg,_))::(Some (true ),_)::[] -> arg
                | (Some (false ),_)::_::[]|_::(Some (false ),_)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____3651 -> tm)
             else
               (let uu____3661 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____3661
                then
                  let uu____3664 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____3664 with
                  | (Some (true ),_)::_::[]|_::(Some (true ),_)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),_)::(_,(arg,_))::[]
                    |(_,(arg,_))::(Some (false ),_)::[] -> arg
                  | uu____3832 -> tm
                else
                  (let uu____3842 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____3842
                   then
                     let uu____3845 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____3845 with
                     | _::(Some (true ),_)::[]|(Some (false ),_)::_::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____3936)::(uu____3937,(arg,uu____3939))::[]
                         -> arg
                     | uu____3980 -> tm
                   else
                     (let uu____3990 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____3990
                      then
                        let uu____3993 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____3993 with
                        | (Some (true ),uu____4028)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____4052)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____4076 -> tm
                      else
                        (let uu____4086 =
                           (FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Syntax_Const.forall_lid)
                             ||
                             (FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid) in
                         if uu____4086
                         then
                           match args with
                           | (t,_)::[]
                             |(_,Some (FStar_Syntax_Syntax.Implicit _))::
                             (t,_)::[] ->
                               let uu____4131 =
                                 let uu____4132 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____4132.FStar_Syntax_Syntax.n in
                               (match uu____4131 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____4137::[],body,uu____4139) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | Some (false ) ->
                                         w FStar_Syntax_Util.t_false
                                     | uu____4167 -> tm)
                                | uu____4169 -> tm)
                           | uu____4170 -> tm
                         else reduce_equality tm))))
         | uu____4177 -> tm)
let is_norm_request hd1 args =
  let uu____4192 =
    let uu____4196 =
      let uu____4197 = FStar_Syntax_Util.un_uinst hd1 in
      uu____4197.FStar_Syntax_Syntax.n in
    (uu____4196, args) in
  match uu____4192 with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4202::uu____4203::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize_term
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4206::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize
  | uu____4208 -> false
let get_norm_request args =
  match args with
  | _::(tm,_)::[]|(tm,_)::[] -> tm
  | uu____4241 -> failwith "Impossible"
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
            (fun uu____4360  ->
               let uu____4361 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____4362 = FStar_Syntax_Print.term_to_string t1 in
               let uu____4363 =
                 let uu____4364 =
                   let uu____4366 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left Prims.fst uu____4366 in
                 stack_to_string uu____4364 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____4361
                 uu____4362 uu____4363);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____4378 ->
               failwith "Impossible"
           | FStar_Syntax_Syntax.Tm_unknown 
             |FStar_Syntax_Syntax.Tm_uvar _
              |FStar_Syntax_Syntax.Tm_constant _
               |FStar_Syntax_Syntax.Tm_name _
                |FStar_Syntax_Syntax.Tm_fvar
                 { FStar_Syntax_Syntax.fv_name = _;
                   FStar_Syntax_Syntax.fv_delta =
                     FStar_Syntax_Syntax.Delta_constant ;
                   FStar_Syntax_Syntax.fv_qual = _;_}
                 |FStar_Syntax_Syntax.Tm_fvar
                  { FStar_Syntax_Syntax.fv_name = _;
                    FStar_Syntax_Syntax.fv_delta = _;
                    FStar_Syntax_Syntax.fv_qual = Some
                      (FStar_Syntax_Syntax.Data_ctor );_}
                  |FStar_Syntax_Syntax.Tm_fvar
                  { FStar_Syntax_Syntax.fv_name = _;
                    FStar_Syntax_Syntax.fv_delta = _;
                    FStar_Syntax_Syntax.fv_qual = Some
                      (FStar_Syntax_Syntax.Record_ctor _);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____4425 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____4425) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Syntax_Const.prims_lid))
               ->
               let tm = get_norm_request args in
               let s =
                 [Reify;
                 Beta;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 Zeta;
                 Iota;
                 Primops] in
               let cfg' =
                 let uu___150_4438 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___150_4438.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant]
                 } in
               let stack' = (Debug t1) ::
                 (Steps ((cfg.steps), (cfg.delta_level))) :: stack1 in
               norm cfg' env stack' tm
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.tk = uu____4442;
                  FStar_Syntax_Syntax.pos = uu____4443;
                  FStar_Syntax_Syntax.vars = uu____4444;_},a1::a2::rest)
               ->
               let uu____4478 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____4478 with
                | (hd1,uu____4489) ->
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
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.tk = uu____4544;
                  FStar_Syntax_Syntax.pos = uu____4545;
                  FStar_Syntax_Syntax.vars = uu____4546;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____4569 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____4569 with
                | (reify_head,uu____4580) ->
                    let a1 =
                      let uu____4596 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (Prims.fst a) in
                      FStar_Syntax_Subst.compress uu____4596 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____4599);
                            FStar_Syntax_Syntax.tk = uu____4600;
                            FStar_Syntax_Syntax.pos = uu____4601;
                            FStar_Syntax_Syntax.vars = uu____4602;_},a2::[])
                         -> norm cfg env stack1 (Prims.fst a2)
                     | uu____4627 ->
                         let stack2 =
                           (App
                              (reify_head, None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____4635 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____4635
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____4642 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____4642
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____4645 =
                      let uu____4649 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____4649, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____4645 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___128_4658  ->
                         match uu___128_4658 with
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining 
                           |FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               if Prims.op_Negation should_delta
               then rebuild cfg env stack1 t1
               else
                 (let r_env =
                    let uu____4662 = FStar_Syntax_Syntax.range_of_fv f in
                    FStar_TypeChecker_Env.set_range cfg.tcenv uu____4662 in
                  let uu____4663 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  match uu____4663 with
                  | None  ->
                      (log cfg
                         (fun uu____4674  ->
                            FStar_Util.print "Tm_fvar case 2\n" []);
                       rebuild cfg env stack1 t1)
                  | Some (us,t2) ->
                      (log cfg
                         (fun uu____4680  ->
                            let uu____4681 =
                              FStar_Syntax_Print.term_to_string t0 in
                            let uu____4682 =
                              FStar_Syntax_Print.term_to_string t2 in
                            FStar_Util.print2 ">>> Unfolded %s to %s\n"
                              uu____4681 uu____4682);
                       (let n1 = FStar_List.length us in
                        if n1 > (Prims.parse_int "0")
                        then
                          match stack1 with
                          | (UnivArgs (us',uu____4689))::stack2 ->
                              let env1 =
                                FStar_All.pipe_right us'
                                  (FStar_List.fold_left
                                     (fun env1  -> fun u  -> (Univ u) :: env1)
                                     env) in
                              norm cfg env1 stack2 t2
                          | uu____4702 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack1 t2
                          | uu____4703 ->
                              let uu____4704 =
                                let uu____4705 =
                                  FStar_Syntax_Print.lid_to_string
                                    (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                FStar_Util.format1
                                  "Impossible: missing universe instantiation on %s"
                                  uu____4705 in
                              failwith uu____4704
                        else norm cfg env stack1 t2)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____4712 = lookup_bvar env x in
               (match uu____4712 with
                | Univ uu____4713 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____4728 = FStar_ST.read r in
                      (match uu____4728 with
                       | Some (env2,t') ->
                           (log cfg
                              (fun uu____4747  ->
                                 let uu____4748 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____4749 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____4748
                                   uu____4749);
                            (let uu____4750 =
                               let uu____4751 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____4751.FStar_Syntax_Syntax.n in
                             match uu____4750 with
                             | FStar_Syntax_Syntax.Tm_abs uu____4754 ->
                                 norm cfg env2 stack1 t'
                             | uu____4769 -> rebuild cfg env2 stack1 t'))
                       | None  -> norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____4802)::uu____4803 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____4808)::uu____4809 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____4815,uu____4816))::stack_rest ->
                    (match c with
                     | Univ uu____4819 -> norm cfg (c :: env) stack_rest t1
                     | uu____4820 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____4823::[] ->
                              (match lopt with
                               | None  when FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____4836  ->
                                         let uu____4837 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____4837);
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
                                           (fun uu___129_4851  ->
                                              match uu___129_4851 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____4852 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____4854  ->
                                         let uu____4855 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____4855);
                                    norm cfg (c :: env) stack_rest body)
                               | Some (FStar_Util.Inl lc) when
                                   FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                                   ->
                                   (log cfg
                                      (fun uu____4866  ->
                                         let uu____4867 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____4867);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____4868 when
                                   FStar_All.pipe_right cfg.steps
                                     (FStar_List.contains Reify)
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____4875 ->
                                   let cfg1 =
                                     let uu___151_4883 = cfg in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___151_4883.tcenv);
                                       delta_level =
                                         (uu___151_4883.delta_level)
                                     } in
                                   let uu____4884 =
                                     closure_as_term cfg1 env t1 in
                                   rebuild cfg1 env stack1 uu____4884)
                          | uu____4885::tl1 ->
                              (log cfg
                                 (fun uu____4895  ->
                                    let uu____4896 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____4896);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,dl))::stack2 ->
                    norm
                      (let uu___152_4917 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___152_4917.tcenv);
                         delta_level = dl
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____4930  ->
                          let uu____4931 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____4931);
                     norm cfg env stack2 t1)
                | (Debug _)::_
                  |(Meta _)::_|(Let _)::_|(App _)::_|(Abs _)::_|[] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____4942 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____4942
                    else
                      (let uu____4944 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____4944 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____4973 =
                                   let uu____4979 =
                                     let uu____4980 =
                                       let uu____4981 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____4981 in
                                     FStar_All.pipe_right uu____4980
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____4979
                                     (fun _0_32  -> FStar_Util.Inl _0_32) in
                                 FStar_All.pipe_right uu____4973
                                   (fun _0_33  -> Some _0_33)
                             | uu____5006 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____5020  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____5025  ->
                                 let uu____5026 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____5026);
                            norm cfg env'
                              ((Abs
                                  (env, bs1, env', lopt1,
                                    (t1.FStar_Syntax_Syntax.pos))) :: stack1)
                              body1)))
           | FStar_Syntax_Syntax.Tm_app (head1,args) ->
               let stack2 =
                 FStar_All.pipe_right stack1
                   (FStar_List.fold_right
                      (fun uu____5060  ->
                         fun stack2  ->
                           match uu____5060 with
                           | (a,aq) ->
                               let uu____5068 =
                                 let uu____5069 =
                                   let uu____5073 =
                                     let uu____5074 =
                                       let uu____5084 =
                                         FStar_Util.mk_ref None in
                                       (env, a, uu____5084, false) in
                                     Clos uu____5074 in
                                   (uu____5073, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____5069 in
                               uu____5068 :: stack2) args) in
               (log cfg
                  (fun uu____5106  ->
                     let uu____5107 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____5107);
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
                             ((let uu___153_5128 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___153_5128.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___153_5128.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____5129 ->
                      let uu____5132 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____5132)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____5135 = FStar_Syntax_Subst.open_term [(x, None)] f in
                  match uu____5135 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____5151 =
                          let uu____5152 =
                            let uu____5157 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___154_5158 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___154_5158.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___154_5158.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____5157) in
                          FStar_Syntax_Syntax.Tm_refine uu____5152 in
                        mk uu____5151 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____5171 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____5171
               else
                 (let uu____5173 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____5173 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____5179 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  -> fun uu____5185  -> Dummy :: env1)
                               env) in
                        norm_comp cfg uu____5179 c1 in
                      let t2 =
                        let uu____5192 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____5192 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,tc,l) ->
               (match stack1 with
                | (Match _)::_
                  |(Arg _)::_
                   |(App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.tk = _;
                       FStar_Syntax_Syntax.pos = _;
                       FStar_Syntax_Syntax.vars = _;_},_,_))::_|(MemoLazy
                    _)::_ -> norm cfg env stack1 t11
                | uu____5231 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____5234  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____5247 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____5247
                        | FStar_Util.Inr c ->
                            let uu____5255 = norm_comp cfg env c in
                            FStar_Util.Inr uu____5255 in
                      let uu____5256 =
                        mk (FStar_Syntax_Syntax.Tm_ascribed (t12, tc1, l))
                          t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____5256)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____5301,{
                              FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                uu____5302;
                              FStar_Syntax_Syntax.lbunivs = uu____5303;
                              FStar_Syntax_Syntax.lbtyp = uu____5304;
                              FStar_Syntax_Syntax.lbeff = uu____5305;
                              FStar_Syntax_Syntax.lbdef = uu____5306;_}::uu____5307),uu____5308)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____5334 =
                 (let uu____5335 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____5335) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____5336 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____5336))) in
               if uu____5334
               then
                 let env1 =
                   let uu____5339 =
                     let uu____5340 =
                       let uu____5350 = FStar_Util.mk_ref None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____5350,
                         false) in
                     Clos uu____5340 in
                   uu____5339 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____5374 =
                    let uu____5377 =
                      let uu____5378 =
                        let uu____5379 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____5379
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____5378] in
                    FStar_Syntax_Subst.open_term uu____5377 body in
                  match uu____5374 with
                  | (bs,body1) ->
                      let lb1 =
                        let uu___155_5385 = lb in
                        let uu____5386 =
                          let uu____5389 =
                            let uu____5390 = FStar_List.hd bs in
                            FStar_All.pipe_right uu____5390 Prims.fst in
                          FStar_All.pipe_right uu____5389
                            (fun _0_34  -> FStar_Util.Inl _0_34) in
                        let uu____5399 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____5402 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = uu____5386;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___155_5385.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____5399;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___155_5385.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5402
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____5412  -> Dummy :: env1)
                             env) in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____5428 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____5428
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____5441 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____5463  ->
                        match uu____5463 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____5502 =
                                let uu___156_5503 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___156_5503.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___156_5503.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____5502 in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos in
                            let memo = FStar_Util.mk_ref None in
                            let rec_env1 = (Clos (env, fix_f_i, memo, true))
                              :: rec_env in
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1")))) (Prims.snd lbs)
                   (env, [], (Prims.parse_int "0")) in
               (match uu____5441 with
                | (rec_env,memos,uu____5563) ->
                    let uu____5578 =
                      FStar_List.map2
                        (fun lb  ->
                           fun memo  ->
                             FStar_ST.write memo
                               (Some
                                  (rec_env, (lb.FStar_Syntax_Syntax.lbdef))))
                        (Prims.snd lbs) memos in
                    let body_env =
                      FStar_List.fold_right
                        (fun lb  ->
                           fun env1  ->
                             let uu____5620 =
                               let uu____5621 =
                                 let uu____5631 = FStar_Util.mk_ref None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____5631, false) in
                               Clos uu____5621 in
                             uu____5620 :: env1) (Prims.snd lbs) env in
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
                             FStar_Syntax_Syntax.tk = uu____5669;
                             FStar_Syntax_Syntax.pos = uu____5670;
                             FStar_Syntax_Syntax.vars = uu____5671;_},uu____5672,uu____5673))::uu____5674
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____5680 -> false in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 = (Steps ((cfg.steps), (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____5686 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____5686
                        then
                          let uu___157_5687 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___157_5687.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only]
                          }
                        else
                          (let uu___158_5689 = cfg in
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___158_5689.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta]
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____5691 =
                         let uu____5692 = FStar_Syntax_Subst.compress head1 in
                         uu____5692.FStar_Syntax_Syntax.n in
                       match uu____5691 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____5706 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____5706 with
                            | (uu____5707,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____5711 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____5718 =
                                         let uu____5719 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____5719.FStar_Syntax_Syntax.n in
                                       match uu____5718 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____5724,uu____5725))
                                           ->
                                           let uu____5734 =
                                             let uu____5735 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____5735.FStar_Syntax_Syntax.n in
                                           (match uu____5734 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____5740,msrc,uu____5742))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____5751 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                Some uu____5751
                                            | uu____5752 -> None)
                                       | uu____5753 -> None in
                                     let uu____5754 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____5754 with
                                      | Some e ->
                                          let lb1 =
                                            let uu___159_5758 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___159_5758.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___159_5758.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___159_5758.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Syntax_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____5759 =
                                            FStar_List.tl stack1 in
                                          let uu____5760 =
                                            let uu____5761 =
                                              let uu____5764 =
                                                let uu____5765 =
                                                  let uu____5773 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____5773) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____5765 in
                                              FStar_Syntax_Syntax.mk
                                                uu____5764 in
                                            uu____5761 None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____5759 uu____5760
                                      | None  ->
                                          let uu____5790 =
                                            let uu____5791 = is_return body in
                                            match uu____5791 with
                                            | Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____5794;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____5795;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____5796;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____5801 -> false in
                                          if uu____5790
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
                                               let uu____5821 =
                                                 let uu____5824 =
                                                   let uu____5825 =
                                                     let uu____5840 =
                                                       let uu____5842 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____5842] in
                                                     (uu____5840, body1,
                                                       (Some
                                                          (FStar_Util.Inr
                                                             (m1, [])))) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____5825 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____5824 in
                                               uu____5821 None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let bind_inst =
                                               let uu____5872 =
                                                 let uu____5873 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____5873.FStar_Syntax_Syntax.n in
                                               match uu____5872 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____5879::uu____5880::[])
                                                   ->
                                                   let uu____5886 =
                                                     let uu____5889 =
                                                       let uu____5890 =
                                                         let uu____5895 =
                                                           let uu____5897 =
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               lb.FStar_Syntax_Syntax.lbtyp in
                                                           let uu____5898 =
                                                             let uu____5900 =
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv t2 in
                                                             [uu____5900] in
                                                           uu____5897 ::
                                                             uu____5898 in
                                                         (bind1, uu____5895) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____5890 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____5889 in
                                                   uu____5886 None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____5912 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____5918 =
                                                 let uu____5921 =
                                                   let uu____5922 =
                                                     let uu____5932 =
                                                       let uu____5934 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____5935 =
                                                         let uu____5937 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____5938 =
                                                           let uu____5940 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____5941 =
                                                             let uu____5943 =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____5944 =
                                                               let uu____5946
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____5947
                                                                 =
                                                                 let uu____5949
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____5949] in
                                                               uu____5946 ::
                                                                 uu____5947 in
                                                             uu____5943 ::
                                                               uu____5944 in
                                                           uu____5940 ::
                                                             uu____5941 in
                                                         uu____5937 ::
                                                           uu____5938 in
                                                       uu____5934 ::
                                                         uu____5935 in
                                                     (bind_inst, uu____5932) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____5922 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____5921 in
                                               uu____5918 None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____5961 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____5961 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____5979 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____5979 with
                            | (uu____5980,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____6003 =
                                        let uu____6004 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____6004.FStar_Syntax_Syntax.n in
                                      match uu____6003 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____6010) -> t4
                                      | uu____6015 -> head2 in
                                    let uu____6016 =
                                      let uu____6017 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____6017.FStar_Syntax_Syntax.n in
                                    match uu____6016 with
                                    | FStar_Syntax_Syntax.Tm_fvar x -> Some x
                                    | uu____6022 -> None in
                                  let uu____6023 = maybe_extract_fv head2 in
                                  match uu____6023 with
                                  | Some x when
                                      let uu____6029 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____6029
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____6033 =
                                          maybe_extract_fv head3 in
                                        match uu____6033 with
                                        | Some uu____6036 -> Some true
                                        | uu____6037 -> Some false in
                                      (head3, action_unfolded)
                                  | uu____6040 -> (head2, None) in
                                ((let is_arg_impure uu____6051 =
                                    match uu____6051 with
                                    | (e,q) ->
                                        let uu____6056 =
                                          let uu____6057 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____6057.FStar_Syntax_Syntax.n in
                                        (match uu____6056 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____6072 -> false) in
                                  let uu____6073 =
                                    let uu____6074 =
                                      let uu____6078 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____6078 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____6074 in
                                  if uu____6073
                                  then
                                    let uu____6081 =
                                      let uu____6082 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____6082 in
                                    failwith uu____6081
                                  else ());
                                 (let uu____6084 =
                                    maybe_unfold_action head_app in
                                  match uu____6084 with
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
                                      let uu____6119 = FStar_List.tl stack1 in
                                      norm cfg env uu____6119 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted = reify_lift cfg.tcenv e msrc mtgt t' in
                           let uu____6133 = FStar_List.tl stack1 in
                           norm cfg env uu____6133 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____6216  ->
                                     match uu____6216 with
                                     | (pat,wopt,tm) ->
                                         let uu____6254 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____6254))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____6280 = FStar_List.tl stack1 in
                           norm cfg env uu____6280 tm
                       | uu____6281 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.tk = uu____6290;
                             FStar_Syntax_Syntax.pos = uu____6291;
                             FStar_Syntax_Syntax.vars = uu____6292;_},uu____6293,uu____6294))::uu____6295
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____6301 -> false in
                    if should_reify
                    then
                      let uu____6302 = FStar_List.tl stack1 in
                      let uu____6303 = reify_lift cfg.tcenv head1 m1 m' t2 in
                      norm cfg env uu____6302 uu____6303
                    else
                      (let uu____6305 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____6305
                       then
                         let stack2 =
                           (Steps ((cfg.steps), (cfg.delta_level))) :: stack1 in
                         let cfg1 =
                           let uu___160_6310 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___160_6310.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only]
                           } in
                         norm cfg1 env
                           ((Meta
                               ((FStar_Syntax_Syntax.Meta_monadic_lift
                                   (m1, m', t2)),
                                 (head1.FStar_Syntax_Syntax.pos))) :: stack2)
                           head1
                       else
                         norm cfg env
                           ((Meta
                               ((FStar_Syntax_Syntax.Meta_monadic_lift
                                   (m1, m', t2)),
                                 (head1.FStar_Syntax_Syntax.pos))) :: stack1)
                           head1)
                | uu____6316 ->
                    (match stack1 with
                     | uu____6317::uu____6318 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____6322)
                              -> norm cfg env ((Meta (m, r)) :: stack1) head1
                          | FStar_Syntax_Syntax.Meta_pattern args ->
                              let args1 = norm_pattern_args cfg env args in
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_pattern args1),
                                      (t1.FStar_Syntax_Syntax.pos))) ::
                                stack1) head1
                          | uu____6337 -> norm cfg env stack1 head1)
                     | [] ->
                         let head2 = norm cfg env [] head1 in
                         let m1 =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               let uu____6347 =
                                 norm_pattern_args cfg env args in
                               FStar_Syntax_Syntax.Meta_pattern uu____6347
                           | uu____6354 -> m in
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
          (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
            FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      fun msrc  ->
        fun mtgt  ->
          fun t  ->
            if FStar_Syntax_Util.is_pure_effect msrc
            then
              let ed = FStar_TypeChecker_Env.get_effect_decl env mtgt in
              let uu____6368 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____6368 with
              | (uu____6369,return_repr) ->
                  let return_inst =
                    let uu____6376 =
                      let uu____6377 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____6377.FStar_Syntax_Syntax.n in
                    match uu____6376 with
                    | FStar_Syntax_Syntax.Tm_uinst (return_tm,uu____6383::[])
                        ->
                        let uu____6389 =
                          let uu____6392 =
                            let uu____6393 =
                              let uu____6398 =
                                let uu____6400 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____6400] in
                              (return_tm, uu____6398) in
                            FStar_Syntax_Syntax.Tm_uinst uu____6393 in
                          FStar_Syntax_Syntax.mk uu____6392 in
                        uu____6389 None e.FStar_Syntax_Syntax.pos
                    | uu____6412 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____6415 =
                    let uu____6418 =
                      let uu____6419 =
                        let uu____6429 =
                          let uu____6431 = FStar_Syntax_Syntax.as_arg t in
                          let uu____6432 =
                            let uu____6434 = FStar_Syntax_Syntax.as_arg e in
                            [uu____6434] in
                          uu____6431 :: uu____6432 in
                        (return_inst, uu____6429) in
                      FStar_Syntax_Syntax.Tm_app uu____6419 in
                    FStar_Syntax_Syntax.mk uu____6418 in
                  uu____6415 None e.FStar_Syntax_Syntax.pos
            else
              (let uu____6447 = FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____6447 with
               | None  ->
                   let uu____6449 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____6449
               | Some
                   { FStar_TypeChecker_Env.msource = uu____6450;
                     FStar_TypeChecker_Env.mtarget = uu____6451;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____6452;
                         FStar_TypeChecker_Env.mlift_term = None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | Some
                   { FStar_TypeChecker_Env.msource = uu____6463;
                     FStar_TypeChecker_Env.mtarget = uu____6464;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____6465;
                         FStar_TypeChecker_Env.mlift_term = Some lift;_};_}
                   ->
                   let uu____6483 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____6483)
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
                (fun uu____6513  ->
                   match uu____6513 with
                   | (a,imp) ->
                       let uu____6520 = norm cfg env [] a in
                       (uu____6520, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___161_6535 = comp1 in
            let uu____6538 =
              let uu____6539 =
                let uu____6545 = norm cfg env [] t in
                let uu____6546 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____6545, uu____6546) in
              FStar_Syntax_Syntax.Total uu____6539 in
            {
              FStar_Syntax_Syntax.n = uu____6538;
              FStar_Syntax_Syntax.tk = (uu___161_6535.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___161_6535.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___161_6535.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___162_6561 = comp1 in
            let uu____6564 =
              let uu____6565 =
                let uu____6571 = norm cfg env [] t in
                let uu____6572 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____6571, uu____6572) in
              FStar_Syntax_Syntax.GTotal uu____6565 in
            {
              FStar_Syntax_Syntax.n = uu____6564;
              FStar_Syntax_Syntax.tk = (uu___162_6561.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___162_6561.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___162_6561.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____6603  ->
                      match uu____6603 with
                      | (a,i) ->
                          let uu____6610 = norm cfg env [] a in
                          (uu____6610, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___130_6615  ->
                      match uu___130_6615 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____6619 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____6619
                      | f -> f)) in
            let uu___163_6623 = comp1 in
            let uu____6626 =
              let uu____6627 =
                let uu___164_6628 = ct in
                let uu____6629 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____6630 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____6633 = norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____6629;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___164_6628.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____6630;
                  FStar_Syntax_Syntax.effect_args = uu____6633;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____6627 in
            {
              FStar_Syntax_Syntax.n = uu____6626;
              FStar_Syntax_Syntax.tk = (uu___163_6623.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___163_6623.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___163_6623.FStar_Syntax_Syntax.vars)
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
            (let uu___165_6650 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___165_6650.tcenv);
               delta_level = (uu___165_6650.delta_level)
             }) env [] t in
        let non_info t =
          let uu____6655 = norm1 t in
          FStar_Syntax_Util.non_informative uu____6655 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____6658 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___166_6672 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.tk = (uu___166_6672.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___166_6672.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___166_6672.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____6682 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____6682
            then
              let ct1 =
                match downgrade_ghost_effect_name
                        ct.FStar_Syntax_Syntax.effect_name
                with
                | Some pure_eff ->
                    let uu___167_6687 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___167_6687.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___167_6687.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___167_6687.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___167_6687.FStar_Syntax_Syntax.flags)
                    }
                | None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___168_6689 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___168_6689.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Syntax_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___168_6689.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___168_6689.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___168_6689.FStar_Syntax_Syntax.flags)
                    } in
              let uu___169_6690 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.tk =
                  (uu___169_6690.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___169_6690.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___169_6690.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____6696 -> c
and norm_binder:
  cfg ->
    env ->
      FStar_Syntax_Syntax.binder ->
        (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  =
  fun cfg  ->
    fun env  ->
      fun uu____6699  ->
        match uu____6699 with
        | (x,imp) ->
            let uu____6702 =
              let uu___170_6703 = x in
              let uu____6704 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___170_6703.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___170_6703.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____6704
              } in
            (uu____6702, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____6710 =
          FStar_List.fold_left
            (fun uu____6717  ->
               fun b  ->
                 match uu____6717 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____6710 with | (nbs,uu____6734) -> FStar_List.rev nbs
and norm_lcomp_opt:
  cfg ->
    env ->
      (FStar_Syntax_Syntax.lcomp,FStar_Syntax_Syntax.residual_comp)
        FStar_Util.either Prims.option ->
        (FStar_Syntax_Syntax.lcomp,FStar_Syntax_Syntax.residual_comp)
          FStar_Util.either Prims.option
  =
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | Some (FStar_Util.Inl lc) ->
            let flags = filter_out_lcomp_cflags lc in
            let uu____6751 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
            if uu____6751
            then
              let t = norm cfg env [] lc.FStar_Syntax_Syntax.res_typ in
              let uu____6756 = FStar_Syntax_Util.is_total_lcomp lc in
              (if uu____6756
               then
                 let uu____6760 =
                   let uu____6763 =
                     let uu____6764 =
                       let uu____6767 = FStar_Syntax_Syntax.mk_Total t in
                       FStar_Syntax_Util.comp_set_flags uu____6767 flags in
                     FStar_Syntax_Util.lcomp_of_comp uu____6764 in
                   FStar_Util.Inl uu____6763 in
                 Some uu____6760
               else
                 (let uu____6771 =
                    let uu____6774 =
                      let uu____6775 =
                        let uu____6778 = FStar_Syntax_Syntax.mk_GTotal t in
                        FStar_Syntax_Util.comp_set_flags uu____6778 flags in
                      FStar_Syntax_Util.lcomp_of_comp uu____6775 in
                    FStar_Util.Inl uu____6774 in
                  Some uu____6771))
            else
              Some
                (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags))
        | uu____6791 -> lopt
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
              ((let uu____6803 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____6803
                then
                  let uu____6804 = FStar_Syntax_Print.term_to_string tm in
                  let uu____6805 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2 "Normalized %s to %s\n" uu____6804
                    uu____6805
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,dl))::stack2 ->
              rebuild
                (let uu___171_6813 = cfg in
                 { steps = s; tcenv = (uu___171_6813.tcenv); delta_level = dl
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____6833  ->
                    let uu____6834 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____6834);
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
              let uu____6871 =
                let uu___172_6872 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___172_6872.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___172_6872.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___172_6872.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____6871
          | (Arg (Univ _,_,_))::_|(Arg (Dummy ,_,_))::_ ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____6894),aq,r))::stack2 ->
              (log cfg
                 (fun uu____6910  ->
                    let uu____6911 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____6911);
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
                 (let uu____6922 = FStar_ST.read m in
                  match uu____6922 with
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
                  | Some (uu____6948,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq) None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.extend_app head1 (t, aq) None r in
              let uu____6970 = maybe_simplify cfg.steps t1 in
              rebuild cfg env stack2 uu____6970
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____6977  ->
                    let uu____6978 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____6978);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____6983 =
                  let whnf = FStar_List.contains WHNF cfg.steps in
                  let cfg_exclude_iota_zeta =
                    let new_delta =
                      FStar_All.pipe_right cfg.delta_level
                        (FStar_List.filter
                           (fun uu___131_6990  ->
                              match uu___131_6990 with
                              | FStar_TypeChecker_Env.Inlining 
                                |FStar_TypeChecker_Env.Eager_unfolding_only 
                                  -> true
                              | uu____6991 -> false)) in
                    let steps' =
                      let uu____6994 =
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains PureSubtermsWithinComputations) in
                      if uu____6994
                      then [Exclude Zeta]
                      else [Exclude Iota; Exclude Zeta] in
                    let uu___173_6997 = cfg in
                    {
                      steps = (FStar_List.append steps' cfg.steps);
                      tcenv = (uu___173_6997.tcenv);
                      delta_level = new_delta
                    } in
                  let norm_or_whnf env2 t1 =
                    if whnf
                    then closure_as_term cfg_exclude_iota_zeta env2 t1
                    else norm cfg_exclude_iota_zeta env2 [] t1 in
                  let rec norm_pat env2 p =
                    match p.FStar_Syntax_Syntax.v with
                    | FStar_Syntax_Syntax.Pat_constant uu____7031 ->
                        (p, env2)
                    | FStar_Syntax_Syntax.Pat_disj [] ->
                        failwith "Impossible"
                    | FStar_Syntax_Syntax.Pat_disj (hd1::tl1) ->
                        let uu____7051 = norm_pat env2 hd1 in
                        (match uu____7051 with
                         | (hd2,env') ->
                             let tl2 =
                               FStar_All.pipe_right tl1
                                 (FStar_List.map
                                    (fun p1  ->
                                       let uu____7087 = norm_pat env2 p1 in
                                       Prims.fst uu____7087)) in
                             ((let uu___174_7099 = p in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_disj (hd2 :: tl2));
                                 FStar_Syntax_Syntax.ty =
                                   (uu___174_7099.FStar_Syntax_Syntax.ty);
                                 FStar_Syntax_Syntax.p =
                                   (uu___174_7099.FStar_Syntax_Syntax.p)
                               }), env'))
                    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                        let uu____7116 =
                          FStar_All.pipe_right pats
                            (FStar_List.fold_left
                               (fun uu____7150  ->
                                  fun uu____7151  ->
                                    match (uu____7150, uu____7151) with
                                    | ((pats1,env3),(p1,b)) ->
                                        let uu____7216 = norm_pat env3 p1 in
                                        (match uu____7216 with
                                         | (p2,env4) ->
                                             (((p2, b) :: pats1), env4)))
                               ([], env2)) in
                        (match uu____7116 with
                         | (pats1,env3) ->
                             ((let uu___175_7282 = p in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_cons
                                      (fv, (FStar_List.rev pats1)));
                                 FStar_Syntax_Syntax.ty =
                                   (uu___175_7282.FStar_Syntax_Syntax.ty);
                                 FStar_Syntax_Syntax.p =
                                   (uu___175_7282.FStar_Syntax_Syntax.p)
                               }), env3))
                    | FStar_Syntax_Syntax.Pat_var x ->
                        let x1 =
                          let uu___176_7296 = x in
                          let uu____7297 =
                            norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___176_7296.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___176_7296.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____7297
                          } in
                        ((let uu___177_7303 = p in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_var x1);
                            FStar_Syntax_Syntax.ty =
                              (uu___177_7303.FStar_Syntax_Syntax.ty);
                            FStar_Syntax_Syntax.p =
                              (uu___177_7303.FStar_Syntax_Syntax.p)
                          }), (Dummy :: env2))
                    | FStar_Syntax_Syntax.Pat_wild x ->
                        let x1 =
                          let uu___178_7308 = x in
                          let uu____7309 =
                            norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___178_7308.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___178_7308.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____7309
                          } in
                        ((let uu___179_7315 = p in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_wild x1);
                            FStar_Syntax_Syntax.ty =
                              (uu___179_7315.FStar_Syntax_Syntax.ty);
                            FStar_Syntax_Syntax.p =
                              (uu___179_7315.FStar_Syntax_Syntax.p)
                          }), (Dummy :: env2))
                    | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                        let x1 =
                          let uu___180_7325 = x in
                          let uu____7326 =
                            norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___180_7325.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___180_7325.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____7326
                          } in
                        let t2 = norm_or_whnf env2 t1 in
                        ((let uu___181_7333 = p in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                            FStar_Syntax_Syntax.ty =
                              (uu___181_7333.FStar_Syntax_Syntax.ty);
                            FStar_Syntax_Syntax.p =
                              (uu___181_7333.FStar_Syntax_Syntax.p)
                          }), env2) in
                  let branches1 =
                    match env1 with
                    | [] when whnf -> branches
                    | uu____7337 ->
                        FStar_All.pipe_right branches
                          (FStar_List.map
                             (fun branch1  ->
                                let uu____7340 =
                                  FStar_Syntax_Subst.open_branch branch1 in
                                match uu____7340 with
                                | (p,wopt,e) ->
                                    let uu____7358 = norm_pat env1 p in
                                    (match uu____7358 with
                                     | (p1,env2) ->
                                         let wopt1 =
                                           match wopt with
                                           | None  -> None
                                           | Some w ->
                                               let uu____7382 =
                                                 norm_or_whnf env2 w in
                                               Some uu____7382 in
                                         let e1 = norm_or_whnf env2 e in
                                         FStar_Syntax_Util.branch
                                           (p1, wopt1, e1)))) in
                  let uu____7387 =
                    mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                      r in
                  rebuild cfg env1 stack2 uu____7387 in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____7397) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant _
                    |FStar_Syntax_Syntax.Tm_fvar
                     { FStar_Syntax_Syntax.fv_name = _;
                       FStar_Syntax_Syntax.fv_delta = _;
                       FStar_Syntax_Syntax.fv_qual = Some
                         (FStar_Syntax_Syntax.Data_ctor );_}
                     |FStar_Syntax_Syntax.Tm_fvar
                     { FStar_Syntax_Syntax.fv_name = _;
                       FStar_Syntax_Syntax.fv_delta = _;
                       FStar_Syntax_Syntax.fv_qual = Some
                         (FStar_Syntax_Syntax.Record_ctor _);_}
                      -> true
                  | uu____7408 -> false in
                let guard_when_clause wopt b rest =
                  match wopt with
                  | None  -> b
                  | Some w ->
                      let then_branch = b in
                      let else_branch =
                        mk (FStar_Syntax_Syntax.Tm_match (scrutinee, rest)) r in
                      FStar_Syntax_Util.if_then_else w then_branch
                        else_branch in
                let rec matches_pat scrutinee1 p =
                  let scrutinee2 = FStar_Syntax_Util.unmeta scrutinee1 in
                  let uu____7507 = FStar_Syntax_Util.head_and_args scrutinee2 in
                  match uu____7507 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_disj ps ->
                           let mopt =
                             FStar_Util.find_map ps
                               (fun p1  ->
                                  let m = matches_pat scrutinee2 p1 in
                                  match m with
                                  | FStar_Util.Inl uu____7564 -> Some m
                                  | FStar_Util.Inr (true ) -> Some m
                                  | FStar_Util.Inr (false ) -> None) in
                           (match mopt with
                            | None  -> FStar_Util.Inr false
                            | Some m -> m)
                       | FStar_Syntax_Syntax.Pat_var _
                         |FStar_Syntax_Syntax.Pat_wild _ ->
                           FStar_Util.Inl [scrutinee2]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____7595 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____7607 ->
                                let uu____7608 =
                                  let uu____7609 = is_cons head1 in
                                  Prims.op_Negation uu____7609 in
                                FStar_Util.Inr uu____7608)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____7623 =
                             let uu____7624 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____7624.FStar_Syntax_Syntax.n in
                           (match uu____7623 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____7631 ->
                                let uu____7632 =
                                  let uu____7633 = is_cons head1 in
                                  Prims.op_Negation uu____7633 in
                                FStar_Util.Inr uu____7632))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____7667)::rest_a,(p1,uu____7670)::rest_p) ->
                      let uu____7698 = matches_pat t1 p1 in
                      (match uu____7698 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____7712 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____7783 = matches_pat scrutinee1 p1 in
                      (match uu____7783 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____7793  ->
                                 let uu____7794 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____7795 =
                                   let uu____7796 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____7796
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____7794 uu____7795);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____7805 =
                                        let uu____7806 =
                                          let uu____7816 =
                                            FStar_Util.mk_ref (Some ([], t1)) in
                                          ([], t1, uu____7816, false) in
                                        Clos uu____7806 in
                                      uu____7805 :: env2) env1 s in
                             let uu____7839 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____7839))) in
                let uu____7840 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____7840
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___132_7854  ->
                match uu___132_7854 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | uu____7857 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____7861 -> d in
      { steps = s; tcenv = e; delta_level = d1 }
let normalize:
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun s  ->
    fun e  ->
      fun t  -> let uu____7872 = config s e in norm uu____7872 [] [] t
let normalize_comp:
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun s  ->
    fun e  ->
      fun t  -> let uu____7882 = config s e in norm_comp uu____7882 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  -> let uu____7889 = config [] env in norm_universe uu____7889 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun c  ->
      let uu____7896 = config [] env in ghost_to_pure_aux uu____7896 [] c
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
        let uu____7908 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____7908 in
      let uu____7909 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____7909
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | Some pure_eff ->
            let uu___182_7911 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___182_7911.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___182_7911.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____7912  ->
                    let uu____7913 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____7913))
            }
        | None  -> lc
      else lc
let term_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun env  ->
    fun t  ->
      let uu____7921 = normalize [AllowUnboundUniverses] env t in
      FStar_Syntax_Print.term_to_string uu____7921
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let uu____7928 =
        let uu____7929 = config [AllowUnboundUniverses] env in
        norm_comp uu____7929 [] c in
      FStar_Syntax_Print.comp_to_string uu____7928
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
                   let uu____7966 =
                     let uu____7967 =
                       let uu____7972 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____7972) in
                     FStar_Syntax_Syntax.Tm_refine uu____7967 in
                   mk uu____7966 t01.FStar_Syntax_Syntax.pos
               | uu____7977 -> t2)
          | uu____7978 -> t2 in
        aux t
let eta_expand_with_type:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun t  ->
    fun sort  ->
      let uu____7985 = FStar_Syntax_Util.arrow_formals_comp sort in
      match uu____7985 with
      | (binders,c) ->
          (match binders with
           | [] -> t
           | uu____8001 ->
               let uu____8005 =
                 FStar_All.pipe_right binders
                   FStar_Syntax_Util.args_of_binders in
               (match uu____8005 with
                | (binders1,args) ->
                    let uu____8015 =
                      (FStar_Syntax_Syntax.mk_Tm_app t args) None
                        t.FStar_Syntax_Syntax.pos in
                    let uu____8020 =
                      let uu____8027 =
                        FStar_All.pipe_right
                          (FStar_Syntax_Util.lcomp_of_comp c)
                          (fun _0_35  -> FStar_Util.Inl _0_35) in
                      FStar_All.pipe_right uu____8027
                        (fun _0_36  -> Some _0_36) in
                    FStar_Syntax_Util.abs binders1 uu____8015 uu____8020))
let eta_expand:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun t  ->
      let uu____8063 =
        let uu____8067 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
        (uu____8067, (t.FStar_Syntax_Syntax.n)) in
      match uu____8063 with
      | (Some sort,uu____8074) ->
          let uu____8076 = mk sort t.FStar_Syntax_Syntax.pos in
          eta_expand_with_type t uu____8076
      | (uu____8077,FStar_Syntax_Syntax.Tm_name x) ->
          eta_expand_with_type t x.FStar_Syntax_Syntax.sort
      | uu____8081 ->
          let uu____8085 = FStar_Syntax_Util.head_and_args t in
          (match uu____8085 with
           | (head1,args) ->
               let uu____8111 =
                 let uu____8112 = FStar_Syntax_Subst.compress head1 in
                 uu____8112.FStar_Syntax_Syntax.n in
               (match uu____8111 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____8115,thead) ->
                    let uu____8129 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____8129 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____8160 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___183_8164 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___183_8164.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___183_8164.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___183_8164.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___183_8164.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___183_8164.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___183_8164.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ = None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___183_8164.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___183_8164.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___183_8164.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___183_8164.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___183_8164.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___183_8164.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___183_8164.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___183_8164.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___183_8164.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___183_8164.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___183_8164.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___183_8164.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___183_8164.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___183_8164.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___183_8164.FStar_TypeChecker_Env.qname_and_index)
                                 }) t in
                            match uu____8160 with
                            | (uu____8165,ty,uu____8167) ->
                                eta_expand_with_type t ty))
                | uu____8168 ->
                    let uu____8169 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___184_8173 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___184_8173.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___184_8173.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___184_8173.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___184_8173.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___184_8173.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___184_8173.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ = None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___184_8173.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___184_8173.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___184_8173.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___184_8173.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___184_8173.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___184_8173.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___184_8173.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___184_8173.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___184_8173.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___184_8173.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___184_8173.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___184_8173.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___184_8173.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___184_8173.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___184_8173.FStar_TypeChecker_Env.qname_and_index)
                         }) t in
                    (match uu____8169 with
                     | (uu____8174,ty,uu____8176) ->
                         eta_expand_with_type t ty)))