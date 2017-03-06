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
  fun uu___124_174  ->
    match uu___124_174 with
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
  fun uu___125_593  ->
    match uu___125_593 with
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
      match uu____662 with | true  -> f () | uu____663 -> ()
let is_empty uu___126_671 =
  match uu___126_671 with | [] -> true | uu____673 -> false
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
    match FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Ghost_lid with
    | true  -> Some FStar_Syntax_Const.effect_Pure_lid
    | uu____699 ->
        (match FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid
         with
         | true  -> Some FStar_Syntax_Const.effect_Tot_lid
         | uu____701 ->
             (match FStar_Ident.lid_equals l
                      FStar_Syntax_Const.effect_GHOST_lid
              with
              | true  -> Some FStar_Syntax_Const.effect_PURE_lid
              | uu____703 -> None))
let norm_universe:
  cfg ->
    closure Prims.list ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun cfg  ->
    fun env  ->
      fun u  ->
        let norm_univs us =
          let us = FStar_Util.sort_with FStar_Syntax_Util.compare_univs us in
          let uu____724 =
            FStar_List.fold_left
              (fun uu____733  ->
                 fun u  ->
                   match uu____733 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____748 = FStar_Syntax_Util.univ_kernel u in
                       (match uu____748 with
                        | (k_u,n) ->
                            let uu____757 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            (match uu____757 with
                             | true  -> (cur_kernel, u, out)
                             | uu____763 -> (k_u, u, (cur_max :: out)))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, []) us in
          match uu____724 with
          | (uu____767,u,out) -> FStar_List.rev (u :: out) in
        let rec aux u =
          let u = FStar_Syntax_Subst.compress_univ u in
          match u with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____783 = FStar_List.nth env x in
                 match uu____783 with
                 | Univ u -> aux u
                 | Dummy  -> [u]
                 | uu____786 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____790 ->
                   let uu____791 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   (match uu____791 with
                    | true  -> [FStar_Syntax_Syntax.U_unknown]
                    | uu____793 -> failwith "Universe variable not found"))
          | FStar_Syntax_Syntax.U_zero 
            |FStar_Syntax_Syntax.U_unif _
             |FStar_Syntax_Syntax.U_name _|FStar_Syntax_Syntax.U_unknown  ->
              [u]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us =
                let uu____801 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____801 norm_univs in
              (match us with
               | u_k::hd::rest ->
                   let rest = hd :: rest in
                   let uu____812 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____812 with
                    | (FStar_Syntax_Syntax.U_zero ,n) ->
                        let uu____817 =
                          FStar_All.pipe_right rest
                            (FStar_List.for_all
                               (fun u  ->
                                  let uu____820 =
                                    FStar_Syntax_Util.univ_kernel u in
                                  match uu____820 with
                                  | (uu____823,m) -> n <= m)) in
                        (match uu____817 with
                         | true  -> rest
                         | uu____826 -> us)
                    | uu____827 -> us)
               | uu____830 -> us)
          | FStar_Syntax_Syntax.U_succ u ->
              let uu____833 = aux u in
              FStar_List.map (fun _0_33  -> FStar_Syntax_Syntax.U_succ _0_33)
                uu____833 in
        let uu____835 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        match uu____835 with
        | true  -> FStar_Syntax_Syntax.U_unknown
        | uu____836 ->
            let uu____837 = aux u in
            (match uu____837 with
             | []|(FStar_Syntax_Syntax.U_zero )::[] ->
                 FStar_Syntax_Syntax.U_zero
             | (FStar_Syntax_Syntax.U_zero )::u::[] -> u
             | (FStar_Syntax_Syntax.U_zero )::us ->
                 FStar_Syntax_Syntax.U_max us
             | u::[] -> u
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
             let t = FStar_Syntax_Subst.compress t in
             (match t.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____940 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown 
                |FStar_Syntax_Syntax.Tm_constant _
                 |FStar_Syntax_Syntax.Tm_name _|FStar_Syntax_Syntax.Tm_fvar _
                  -> t
              | FStar_Syntax_Syntax.Tm_uvar uu____964 -> t
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____974 =
                    let uu____975 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____975 in
                  mk uu____974 t.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
                  let uu____982 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t uu____982
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____984 = lookup_bvar env x in
                  (match uu____984 with
                   | Univ uu____985 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t
                   | Clos (env,t0,r,uu____989) -> closure_as_term cfg env t0)
              | FStar_Syntax_Syntax.Tm_app (head,args) ->
                  let head = closure_as_term_delayed cfg env head in
                  let args = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head, args))
                    t.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____1057 = closures_as_binders_delayed cfg env bs in
                  (match uu____1057 with
                   | (bs,env) ->
                       let body = closure_as_term_delayed cfg env body in
                       let uu____1077 =
                         let uu____1078 =
                           let uu____1093 = close_lcomp_opt cfg env lopt in
                           (bs, body, uu____1093) in
                         FStar_Syntax_Syntax.Tm_abs uu____1078 in
                       mk uu____1077 t.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____1123 = closures_as_binders_delayed cfg env bs in
                  (match uu____1123 with
                   | (bs,env) ->
                       let c = close_comp cfg env c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                         t.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____1154 =
                    let uu____1161 =
                      let uu____1165 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____1165] in
                    closures_as_binders_delayed cfg env uu____1161 in
                  (match uu____1154 with
                   | (x,env) ->
                       let phi = closure_as_term_delayed cfg env phi in
                       let uu____1179 =
                         let uu____1180 =
                           let uu____1185 =
                             let uu____1186 = FStar_List.hd x in
                             FStar_All.pipe_right uu____1186 Prims.fst in
                           (uu____1185, phi) in
                         FStar_Syntax_Syntax.Tm_refine uu____1180 in
                       mk uu____1179 t.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t1,FStar_Util.Inl t2,lopt)
                  ->
                  let uu____1216 =
                    let uu____1217 =
                      let uu____1230 = closure_as_term_delayed cfg env t1 in
                      let uu____1233 =
                        let uu____1240 = closure_as_term_delayed cfg env t2 in
                        FStar_All.pipe_left
                          (fun _0_34  -> FStar_Util.Inl _0_34) uu____1240 in
                      (uu____1230, uu____1233, lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____1217 in
                  mk uu____1216 t.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_ascribed (t1,FStar_Util.Inr c,lopt) ->
                  let uu____1285 =
                    let uu____1286 =
                      let uu____1299 = closure_as_term_delayed cfg env t1 in
                      let uu____1302 =
                        let uu____1309 = close_comp cfg env c in
                        FStar_All.pipe_left
                          (fun _0_35  -> FStar_Util.Inr _0_35) uu____1309 in
                      (uu____1299, uu____1302, lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____1286 in
                  mk uu____1285 t.FStar_Syntax_Syntax.pos
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
                  mk uu____1345 t.FStar_Syntax_Syntax.pos
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
                  mk uu____1397 t.FStar_Syntax_Syntax.pos
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
                  mk uu____1431 t.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____1460 =
                    let uu____1461 =
                      let uu____1466 = closure_as_term_delayed cfg env t' in
                      (uu____1466, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____1461 in
                  mk uu____1460 t.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env =
                    FStar_List.fold_left
                      (fun env  -> fun uu____1487  -> Dummy :: env) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef in
                  let body =
                    match lb.FStar_Syntax_Syntax.lbname with
                    | FStar_Util.Inr uu____1498 -> body
                    | FStar_Util.Inl uu____1499 ->
                        closure_as_term cfg (Dummy :: env0) body in
                  let lb =
                    let uu___138_1501 = lb in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___138_1501.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___138_1501.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = typ;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___138_1501.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = def
                    } in
                  mk (FStar_Syntax_Syntax.Tm_let ((false, [lb]), body))
                    t.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((uu____1508,lbs),body) ->
                  let norm_one_lb env lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____1532  -> fun env  -> Dummy :: env)
                        lb.FStar_Syntax_Syntax.lbunivs env in
                    let env =
                      let uu____1537 = FStar_Syntax_Syntax.is_top_level lbs in
                      match uu____1537 with
                      | true  -> env_univs
                      | uu____1539 ->
                          FStar_List.fold_right
                            (fun uu____1541  -> fun env  -> Dummy :: env) lbs
                            env_univs in
                    let uu___139_1544 = lb in
                    let uu____1545 =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let uu____1548 =
                      closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___139_1544.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___139_1544.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = uu____1545;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___139_1544.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____1548
                    } in
                  let lbs =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____1559  -> fun env  -> Dummy :: env) lbs env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                    t.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head,branches) ->
                  let head = closure_as_term cfg env head in
                  let norm_one_branch env uu____1614 =
                    match uu____1614 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____1660 ->
                              (p, env)
                          | FStar_Syntax_Syntax.Pat_disj [] ->
                              failwith "Impossible"
                          | FStar_Syntax_Syntax.Pat_disj (hd::tl) ->
                              let uu____1680 = norm_pat env hd in
                              (match uu____1680 with
                               | (hd,env') ->
                                   let tl =
                                     FStar_All.pipe_right tl
                                       (FStar_List.map
                                          (fun p  ->
                                             let uu____1716 = norm_pat env p in
                                             Prims.fst uu____1716)) in
                                   ((let uu___140_1728 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_disj (hd ::
                                            tl));
                                       FStar_Syntax_Syntax.ty =
                                         (uu___140_1728.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___140_1728.FStar_Syntax_Syntax.p)
                                     }), env'))
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____1745 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____1779  ->
                                        fun uu____1780  ->
                                          match (uu____1779, uu____1780) with
                                          | ((pats,env),(p,b)) ->
                                              let uu____1845 = norm_pat env p in
                                              (match uu____1845 with
                                               | (p,env) ->
                                                   (((p, b) :: pats), env)))
                                     ([], env)) in
                              (match uu____1745 with
                               | (pats,env) ->
                                   ((let uu___141_1911 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats)));
                                       FStar_Syntax_Syntax.ty =
                                         (uu___141_1911.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___141_1911.FStar_Syntax_Syntax.p)
                                     }), env))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x =
                                let uu___142_1925 = x in
                                let uu____1926 =
                                  closure_as_term cfg env
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___142_1925.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___142_1925.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1926
                                } in
                              ((let uu___143_1932 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___143_1932.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___143_1932.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x =
                                let uu___144_1937 = x in
                                let uu____1938 =
                                  closure_as_term cfg env
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___144_1937.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___144_1937.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1938
                                } in
                              ((let uu___145_1944 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___145_1944.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___145_1944.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t) ->
                              let x =
                                let uu___146_1954 = x in
                                let uu____1955 =
                                  closure_as_term cfg env
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___146_1954.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___146_1954.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1955
                                } in
                              let t = closure_as_term cfg env t in
                              ((let uu___147_1962 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term (x, t));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___147_1962.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___147_1962.FStar_Syntax_Syntax.p)
                                }), env) in
                        let uu____1965 = norm_pat env pat in
                        (match uu____1965 with
                         | (pat,env) ->
                             let w_opt =
                               match w_opt with
                               | None  -> None
                               | Some w ->
                                   let uu____1989 = closure_as_term cfg env w in
                                   Some uu____1989 in
                             let tm = closure_as_term cfg env tm in
                             (pat, w_opt, tm)) in
                  let uu____1994 =
                    let uu____1995 =
                      let uu____2011 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head, uu____2011) in
                    FStar_Syntax_Syntax.Tm_match uu____1995 in
                  mk uu____1994 t.FStar_Syntax_Syntax.pos))
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
                    | ((env,out),(b,imp)) ->
                        let b =
                          let uu___148_2186 = b in
                          let uu____2187 =
                            closure_as_term_delayed cfg env
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___148_2186.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___148_2186.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____2187
                          } in
                        let env = Dummy :: env in (env, ((b, imp) :: out)))
               (env, [])) in
        match uu____2117 with | (env,bs) -> ((FStar_List.rev bs), env)
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
             | FStar_Syntax_Syntax.Comp c ->
                 let rt =
                   closure_as_term_delayed cfg env
                     c.FStar_Syntax_Syntax.result_typ in
                 let args =
                   closures_as_args_delayed cfg env
                     c.FStar_Syntax_Syntax.effect_args in
                 let flags =
                   FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___127_2274  ->
                           match uu___127_2274 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____2278 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____2278
                           | f -> f)) in
                 let uu____2282 =
                   let uu___149_2283 = c in
                   let uu____2284 =
                     FStar_List.map (norm_universe cfg env)
                       c.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____2284;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___149_2283.FStar_Syntax_Syntax.effect_name);
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
         (fun uu___128_2288  ->
            match uu___128_2288 with
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
            (match uu____2320 with
             | true  ->
                 Some
                   (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, flags))
             | uu____2336 ->
                 let uu____2337 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
                 (match uu____2337 with
                  | true  ->
                      Some
                        (FStar_Util.Inr
                           (FStar_Syntax_Const.effect_GTot_lid, flags))
                  | uu____2353 ->
                      Some
                        (FStar_Util.Inr
                           ((lc.FStar_Syntax_Syntax.eff_name), flags))))
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
  let mk x = mk x FStar_Range.dummyRange in
  let name x =
    let uu____2668 =
      let uu____2669 =
        let uu____2670 = FStar_Syntax_Const.p2l x in
        FStar_Syntax_Syntax.lid_as_fv uu____2670
          FStar_Syntax_Syntax.Delta_constant None in
      FStar_Syntax_Syntax.Tm_fvar uu____2669 in
    mk uu____2668 in
  let ctor x =
    let uu____2679 =
      let uu____2680 =
        let uu____2681 = FStar_Syntax_Const.p2l x in
        FStar_Syntax_Syntax.lid_as_fv uu____2681
          FStar_Syntax_Syntax.Delta_constant
          (Some FStar_Syntax_Syntax.Data_ctor) in
      FStar_Syntax_Syntax.Tm_fvar uu____2680 in
    mk uu____2679 in
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
           mk uu____2700 in
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
                            mk
                              (FStar_Syntax_Syntax.Tm_constant
                                 (FStar_Const.Const_char c)) in
                          (uu____2799, None) in
                        [uu____2793; (a, None)] in
                      uu____2774 :: uu____2786 in
                    (uu____2765, uu____2767) in
                  FStar_Syntax_Syntax.Tm_app uu____2755 in
                mk uu____2754) uu____2695 uu____2697)) in
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
  | FStar_Syntax_Syntax.Tm_fvar fv ->
      FStar_List.tryFind
        (fun uu____3026  ->
           match uu____3026 with
           | (l,uu____3030) -> FStar_Syntax_Syntax.fv_eq_lid fv l) ops
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
      match uu____3048 with
      | true  -> tm
      | uu____3051 ->
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
                             let uu____3203 =
                               FStar_Syntax_Subst.compress head1 in
                             uu____3203.FStar_Syntax_Syntax.n in
                           let uu____3206 =
                             let uu____3207 =
                               FStar_Syntax_Subst.compress head2 in
                             uu____3207.FStar_Syntax_Syntax.n in
                           let uu____3210 =
                             let uu____3211 =
                               FStar_Syntax_Subst.compress arg1 in
                             uu____3211.FStar_Syntax_Syntax.n in
                           let uu____3214 =
                             let uu____3215 =
                               FStar_Syntax_Subst.compress arg2 in
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
                     | (FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_int
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
                         let uu____3363 =
                           FStar_Bytes.unicode_bytes_as_string b in
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
        let uu___150_3390 = t in
        {
          FStar_Syntax_Syntax.n = (uu___150_3390.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___150_3390.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___150_3390.FStar_Syntax_Syntax.vars)
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
      match uu____3436 with
      | true  -> reduce_primops steps tm
      | uu____3439 ->
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
               (match uu____3480 with
                | true  ->
                    let uu____3483 =
                      FStar_All.pipe_right args (FStar_List.map simplify) in
                    (match uu____3483 with
                     | (Some (true ),_)::(_,(arg,_))::[]
                       |(_,(arg,_))::(Some (true ),_)::[] -> arg
                     | (Some (false ),_)::_::[]|_::(Some (false ),_)::[] ->
                         w FStar_Syntax_Util.t_false
                     | uu____3651 -> tm)
                | uu____3660 ->
                    let uu____3661 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Syntax_Const.or_lid in
                    (match uu____3661 with
                     | true  ->
                         let uu____3664 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify) in
                         (match uu____3664 with
                          | (Some (true ),_)::_::[]|_::(Some (true ),_)::[]
                              -> w FStar_Syntax_Util.t_true
                          | (Some (false ),_)::(_,(arg,_))::[]
                            |(_,(arg,_))::(Some (false ),_)::[] -> arg
                          | uu____3832 -> tm)
                     | uu____3841 ->
                         let uu____3842 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.imp_lid in
                         (match uu____3842 with
                          | true  ->
                              let uu____3845 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify) in
                              (match uu____3845 with
                               | _::(Some (true ),_)::[]
                                 |(Some (false ),_)::_::[] ->
                                   w FStar_Syntax_Util.t_true
                               | (Some (true ),uu____3936)::(uu____3937,
                                                             (arg,uu____3939))::[]
                                   -> arg
                               | uu____3980 -> tm)
                          | uu____3989 ->
                              let uu____3990 =
                                FStar_Syntax_Syntax.fv_eq_lid fv
                                  FStar_Syntax_Const.not_lid in
                              (match uu____3990 with
                               | true  ->
                                   let uu____3993 =
                                     FStar_All.pipe_right args
                                       (FStar_List.map simplify) in
                                   (match uu____3993 with
                                    | (Some (true ),uu____4028)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (Some (false ),uu____4052)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____4076 -> tm)
                               | uu____4085 ->
                                   let uu____4086 =
                                     (FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Syntax_Const.forall_lid)
                                       ||
                                       (FStar_Syntax_Syntax.fv_eq_lid fv
                                          FStar_Syntax_Const.exists_lid) in
                                   (match uu____4086 with
                                    | true  ->
                                        (match args with
                                         | (t,_)::[]
                                           |(_,Some
                                             (FStar_Syntax_Syntax.Implicit
                                             _))::(t,_)::[] ->
                                             let uu____4131 =
                                               let uu____4132 =
                                                 FStar_Syntax_Subst.compress
                                                   t in
                                               uu____4132.FStar_Syntax_Syntax.n in
                                             (match uu____4131 with
                                              | FStar_Syntax_Syntax.Tm_abs
                                                  (uu____4137::[],body,uu____4139)
                                                  ->
                                                  (match simp_t body with
                                                   | Some (true ) ->
                                                       w
                                                         FStar_Syntax_Util.t_true
                                                   | Some (false ) ->
                                                       w
                                                         FStar_Syntax_Util.t_false
                                                   | uu____4167 -> tm)
                                              | uu____4169 -> tm)
                                         | uu____4170 -> tm)
                                    | uu____4176 -> reduce_equality tm)))))
           | uu____4177 -> tm)
let is_norm_request hd args =
  let uu____4192 =
    let uu____4196 =
      let uu____4197 = FStar_Syntax_Util.un_uinst hd in
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
      fun stack  ->
        fun t  ->
          let t = FStar_Syntax_Subst.compress t in
          let firstn k l =
            match (FStar_List.length l) < k with
            | true  -> (l, [])
            | uu____4358 -> FStar_Util.first_N k l in
          log cfg
            (fun uu____4360  ->
               let uu____4361 = FStar_Syntax_Print.tag_of_term t in
               let uu____4362 = FStar_Syntax_Print.term_to_string t in
               let uu____4363 =
                 let uu____4364 =
                   let uu____4366 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left Prims.fst uu____4366 in
                 stack_to_string uu____4364 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____4361
                 uu____4362 uu____4363);
          (match t.FStar_Syntax_Syntax.n with
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
               -> rebuild cfg env stack t
           | FStar_Syntax_Syntax.Tm_app (hd,args) when
               ((let uu____4425 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____4425) && (is_norm_request hd args))
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
                 let uu___151_4438 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___151_4438.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant]
                 } in
               let stack' = (Debug t) ::
                 (Steps ((cfg.steps), (cfg.delta_level))) :: stack in
               norm cfg' env stack' tm
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.tk = uu____4442;
                  FStar_Syntax_Syntax.pos = uu____4443;
                  FStar_Syntax_Syntax.vars = uu____4444;_},a1::a2::rest)
               ->
               let uu____4478 = FStar_Syntax_Util.head_and_args t in
               (match uu____4478 with
                | (hd,uu____4489) ->
                    let t' =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_app (hd, [a1])) None
                        t.FStar_Syntax_Syntax.pos in
                    let t =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_app (t', (a2 :: rest))) None
                        t.FStar_Syntax_Syntax.pos in
                    norm cfg env stack t)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.tk = uu____4544;
                  FStar_Syntax_Syntax.pos = uu____4545;
                  FStar_Syntax_Syntax.vars = uu____4546;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____4569 = FStar_Syntax_Util.head_and_args t in
               (match uu____4569 with
                | (reify_head,uu____4580) ->
                    let a =
                      let uu____4596 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (Prims.fst a) in
                      FStar_Syntax_Subst.compress uu____4596 in
                    (match a.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____4599);
                            FStar_Syntax_Syntax.tk = uu____4600;
                            FStar_Syntax_Syntax.pos = uu____4601;
                            FStar_Syntax_Syntax.vars = uu____4602;_},a::[])
                         -> norm cfg env stack (Prims.fst a)
                     | uu____4627 ->
                         let stack =
                           (App
                              (reify_head, None, (t.FStar_Syntax_Syntax.pos)))
                           :: stack in
                         norm cfg env stack a))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u = norm_universe cfg env u in
               let uu____4635 =
                 mk (FStar_Syntax_Syntax.Tm_type u) t.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____4635
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____4642 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               (match uu____4642 with
                | true  -> norm cfg env stack t'
                | uu____4643 ->
                    let us =
                      let uu____4645 =
                        let uu____4649 =
                          FStar_List.map (norm_universe cfg env) us in
                        (uu____4649, (t.FStar_Syntax_Syntax.pos)) in
                      UnivArgs uu____4645 in
                    let stack = us :: stack in norm cfg env stack t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___129_4658  ->
                         match uu___129_4658 with
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining 
                           |FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               (match Prims.op_Negation should_delta with
                | true  -> rebuild cfg env stack t
                | uu____4660 ->
                    let r_env =
                      let uu____4662 = FStar_Syntax_Syntax.range_of_fv f in
                      FStar_TypeChecker_Env.set_range cfg.tcenv uu____4662 in
                    let uu____4663 =
                      FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                        r_env
                        (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                    (match uu____4663 with
                     | None  ->
                         (log cfg
                            (fun uu____4674  ->
                               FStar_Util.print "Tm_fvar case 2\n" []);
                          rebuild cfg env stack t)
                     | Some (us,t) ->
                         (log cfg
                            (fun uu____4680  ->
                               let uu____4681 =
                                 FStar_Syntax_Print.term_to_string t0 in
                               let uu____4682 =
                                 FStar_Syntax_Print.term_to_string t in
                               FStar_Util.print2 ">>> Unfolded %s to %s\n"
                                 uu____4681 uu____4682);
                          (let n = FStar_List.length us in
                           match n > (Prims.parse_int "0") with
                           | true  ->
                               (match stack with
                                | (UnivArgs (us',uu____4689))::stack ->
                                    let env =
                                      FStar_All.pipe_right us'
                                        (FStar_List.fold_left
                                           (fun env  ->
                                              fun u  -> (Univ u) :: env) env) in
                                    norm cfg env stack t
                                | uu____4702 when
                                    FStar_All.pipe_right cfg.steps
                                      (FStar_List.contains EraseUniverses)
                                    -> norm cfg env stack t
                                | uu____4703 ->
                                    let uu____4704 =
                                      let uu____4705 =
                                        FStar_Syntax_Print.lid_to_string
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                      FStar_Util.format1
                                        "Impossible: missing universe instantiation on %s"
                                        uu____4705 in
                                    failwith uu____4704)
                           | uu____4710 -> norm cfg env stack t))))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____4712 = lookup_bvar env x in
               (match uu____4712 with
                | Univ uu____4713 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env,t0,r,fix) ->
                    (match (Prims.op_Negation fix) ||
                             (Prims.op_Negation
                                (FStar_List.contains (Exclude Zeta) cfg.steps))
                     with
                     | true  ->
                         let uu____4728 = FStar_ST.read r in
                         (match uu____4728 with
                          | Some (env,t') ->
                              (log cfg
                                 (fun uu____4747  ->
                                    let uu____4748 =
                                      FStar_Syntax_Print.term_to_string t in
                                    let uu____4749 =
                                      FStar_Syntax_Print.term_to_string t' in
                                    FStar_Util.print2
                                      "Lazy hit: %s cached to %s\n"
                                      uu____4748 uu____4749);
                               (let uu____4750 =
                                  let uu____4751 =
                                    FStar_Syntax_Subst.compress t' in
                                  uu____4751.FStar_Syntax_Syntax.n in
                                match uu____4750 with
                                | FStar_Syntax_Syntax.Tm_abs uu____4754 ->
                                    norm cfg env stack t'
                                | uu____4769 -> rebuild cfg env stack t'))
                          | None  -> norm cfg env ((MemoLazy r) :: stack) t0)
                     | uu____4776 -> norm cfg env stack t0))
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____4802)::uu____4803 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____4808)::uu____4809 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____4815,uu____4816))::stack_rest ->
                    (match c with
                     | Univ uu____4819 -> norm cfg (c :: env) stack_rest t
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
                                           (fun uu___130_4851  ->
                                              match uu___130_4851 with
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
                                   let cfg =
                                     let uu___152_4883 = cfg in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___152_4883.tcenv);
                                       delta_level =
                                         (uu___152_4883.delta_level)
                                     } in
                                   let uu____4884 = closure_as_term cfg env t in
                                   rebuild cfg env stack uu____4884)
                          | uu____4885::tl ->
                              (log cfg
                                 (fun uu____4895  ->
                                    let uu____4896 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____4896);
                               (let body =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl, body, lopt))
                                    t.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body))))
                | (Steps (s,dl))::stack ->
                    norm
                      (let uu___153_4917 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___153_4917.tcenv);
                         delta_level = dl
                       }) env stack t
                | (MemoLazy r)::stack ->
                    (set_memo r (env, t);
                     log cfg
                       (fun uu____4930  ->
                          let uu____4931 =
                            FStar_Syntax_Print.term_to_string t in
                          FStar_Util.print1 "\tSet memo %s\n" uu____4931);
                     norm cfg env stack t)
                | (Debug _)::_
                  |(Meta _)::_|(Let _)::_|(App _)::_|(Abs _)::_|[] ->
                    (match FStar_List.contains WHNF cfg.steps with
                     | true  ->
                         let uu____4942 = closure_as_term cfg env t in
                         rebuild cfg env stack uu____4942
                     | uu____4943 ->
                         let uu____4944 =
                           FStar_Syntax_Subst.open_term' bs body in
                         (match uu____4944 with
                          | (bs,body,opening) ->
                              let lopt =
                                match lopt with
                                | Some (FStar_Util.Inl l) ->
                                    let uu____4973 =
                                      let uu____4979 =
                                        let uu____4980 =
                                          let uu____4981 =
                                            l.FStar_Syntax_Syntax.comp () in
                                          FStar_Syntax_Subst.subst_comp
                                            opening uu____4981 in
                                        FStar_All.pipe_right uu____4980
                                          FStar_Syntax_Util.lcomp_of_comp in
                                      FStar_All.pipe_right uu____4979
                                        (fun _0_36  -> FStar_Util.Inl _0_36) in
                                    FStar_All.pipe_right uu____4973
                                      (fun _0_37  -> Some _0_37)
                                | uu____5006 -> lopt in
                              let env' =
                                FStar_All.pipe_right bs
                                  (FStar_List.fold_left
                                     (fun env  ->
                                        fun uu____5020  -> Dummy :: env) env) in
                              (log cfg
                                 (fun uu____5025  ->
                                    let uu____5026 =
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int
                                        (FStar_List.length bs) in
                                    FStar_Util.print1
                                      "\tShifted %s dummies\n" uu____5026);
                               norm cfg env'
                                 ((Abs
                                     (env, bs, env', lopt,
                                       (t.FStar_Syntax_Syntax.pos))) ::
                                 stack) body))))
           | FStar_Syntax_Syntax.Tm_app (head,args) ->
               let stack =
                 FStar_All.pipe_right stack
                   (FStar_List.fold_right
                      (fun uu____5060  ->
                         fun stack  ->
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
                                     (t.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____5069 in
                               uu____5068 :: stack) args) in
               (log cfg
                  (fun uu____5106  ->
                     let uu____5107 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____5107);
                norm cfg env stack head)
           | FStar_Syntax_Syntax.Tm_refine (x,f) ->
               (match FStar_List.contains WHNF cfg.steps with
                | true  ->
                    (match (env, stack) with
                     | ([],[]) ->
                         let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                         let t =
                           mk
                             (FStar_Syntax_Syntax.Tm_refine
                                ((let uu___154_5128 = x in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___154_5128.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___154_5128.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = t_x
                                  }), f)) t.FStar_Syntax_Syntax.pos in
                         rebuild cfg env stack t
                     | uu____5129 ->
                         let uu____5132 = closure_as_term cfg env t in
                         rebuild cfg env stack uu____5132)
                | uu____5133 ->
                    let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                    let uu____5135 =
                      FStar_Syntax_Subst.open_term [(x, None)] f in
                    (match uu____5135 with
                     | (closing,f) ->
                         let f = norm cfg (Dummy :: env) [] f in
                         let t =
                           let uu____5151 =
                             let uu____5152 =
                               let uu____5157 =
                                 FStar_Syntax_Subst.close closing f in
                               ((let uu___155_5158 = x in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___155_5158.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___155_5158.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = t_x
                                 }), uu____5157) in
                             FStar_Syntax_Syntax.Tm_refine uu____5152 in
                           mk uu____5151 t.FStar_Syntax_Syntax.pos in
                         rebuild cfg env stack t))
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               (match FStar_List.contains WHNF cfg.steps with
                | true  ->
                    let uu____5171 = closure_as_term cfg env t in
                    rebuild cfg env stack uu____5171
                | uu____5172 ->
                    let uu____5173 = FStar_Syntax_Subst.open_comp bs c in
                    (match uu____5173 with
                     | (bs,c) ->
                         let c =
                           let uu____5179 =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env  ->
                                     fun uu____5185  -> Dummy :: env) env) in
                           norm_comp cfg uu____5179 c in
                         let t =
                           let uu____5192 = norm_binders cfg env bs in
                           FStar_Syntax_Util.arrow uu____5192 c in
                         rebuild cfg env stack t))
           | FStar_Syntax_Syntax.Tm_ascribed (t1,tc,l) ->
               (match stack with
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
                    _)::_ -> norm cfg env stack t1
                | uu____5231 ->
                    let t1 = norm cfg env [] t1 in
                    (log cfg
                       (fun uu____5234  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc =
                        match tc with
                        | FStar_Util.Inl t ->
                            let uu____5247 = norm cfg env [] t in
                            FStar_Util.Inl uu____5247
                        | FStar_Util.Inr c ->
                            let uu____5255 = norm_comp cfg env c in
                            FStar_Util.Inr uu____5255 in
                      let uu____5256 =
                        mk (FStar_Syntax_Syntax.Tm_ascribed (t1, tc, l))
                          t.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack uu____5256)))
           | FStar_Syntax_Syntax.Tm_match (head,branches) ->
               let stack =
                 (Match (env, branches, (t.FStar_Syntax_Syntax.pos))) ::
                 stack in
               norm cfg env stack head
           | FStar_Syntax_Syntax.Tm_let
               ((uu____5301,{
                              FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                uu____5302;
                              FStar_Syntax_Syntax.lbunivs = uu____5303;
                              FStar_Syntax_Syntax.lbtyp = uu____5304;
                              FStar_Syntax_Syntax.lbeff = uu____5305;
                              FStar_Syntax_Syntax.lbdef = uu____5306;_}::uu____5307),uu____5308)
               -> rebuild cfg env stack t
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____5334 =
                 (let uu____5335 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____5335) &&
                   ((FStar_Syntax_Util.is_pure_effect n) ||
                      ((FStar_Syntax_Util.is_ghost_effect n) &&
                         (let uu____5336 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____5336))) in
               (match uu____5334 with
                | true  ->
                    let env =
                      let uu____5339 =
                        let uu____5340 =
                          let uu____5350 = FStar_Util.mk_ref None in
                          (env, (lb.FStar_Syntax_Syntax.lbdef), uu____5350,
                            false) in
                        Clos uu____5340 in
                      uu____5339 :: env in
                    norm cfg env stack body
                | uu____5373 ->
                    let uu____5374 =
                      let uu____5377 =
                        let uu____5378 =
                          let uu____5379 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left in
                          FStar_All.pipe_right uu____5379
                            FStar_Syntax_Syntax.mk_binder in
                        [uu____5378] in
                      FStar_Syntax_Subst.open_term uu____5377 body in
                    (match uu____5374 with
                     | (bs,body) ->
                         let lb =
                           let uu___156_5385 = lb in
                           let uu____5386 =
                             let uu____5389 =
                               let uu____5390 = FStar_List.hd bs in
                               FStar_All.pipe_right uu____5390 Prims.fst in
                             FStar_All.pipe_right uu____5389
                               (fun _0_38  -> FStar_Util.Inl _0_38) in
                           let uu____5399 =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let uu____5402 =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname = uu____5386;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___156_5385.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = uu____5399;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___156_5385.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____5402
                           } in
                         let env' =
                           FStar_All.pipe_right bs
                             (FStar_List.fold_left
                                (fun env  -> fun uu____5412  -> Dummy :: env)
                                env) in
                         norm cfg env'
                           ((Let (env, bs, lb, (t.FStar_Syntax_Syntax.pos)))
                           :: stack) body))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____5428 = closure_as_term cfg env t in
               rebuild cfg env stack uu____5428
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____5441 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____5463  ->
                        match uu____5463 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____5502 =
                                let uu___157_5503 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___157_5503.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___157_5503.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____5502 in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t.FStar_Syntax_Syntax.pos in
                            let memo = FStar_Util.mk_ref None in
                            let rec_env = (Clos (env, fix_f_i, memo, true))
                              :: rec_env in
                            (rec_env, (memo :: memos),
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
                           fun env  ->
                             let uu____5620 =
                               let uu____5621 =
                                 let uu____5631 = FStar_Util.mk_ref None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____5631, false) in
                               Clos uu____5621 in
                             uu____5620 :: env) (Prims.snd lbs) env in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head,m) ->
               (match m with
                | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
                    let should_reify =
                      match stack with
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
                    (match Prims.op_Negation should_reify with
                     | true  ->
                         let t = norm cfg env [] t in
                         let stack = (Steps ((cfg.steps), (cfg.delta_level)))
                           :: stack in
                         let cfg =
                           let uu___158_5686 = cfg in
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___158_5686.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta]
                           } in
                         norm cfg env
                           ((Meta
                               ((FStar_Syntax_Syntax.Meta_monadic (m, t)),
                                 (t.FStar_Syntax_Syntax.pos))) :: stack) head
                     | uu____5687 ->
                         let uu____5688 =
                           let uu____5689 = FStar_Syntax_Subst.compress head in
                           uu____5689.FStar_Syntax_Syntax.n in
                         (match uu____5688 with
                          | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body)
                              ->
                              let ed =
                                FStar_TypeChecker_Env.get_effect_decl
                                  cfg.tcenv m in
                              let uu____5703 =
                                ed.FStar_Syntax_Syntax.bind_repr in
                              (match uu____5703 with
                               | (uu____5704,bind_repr) ->
                                   (match lb.FStar_Syntax_Syntax.lbname with
                                    | FStar_Util.Inr uu____5708 ->
                                        failwith
                                          "Cannot reify a top-level let binding"
                                    | FStar_Util.Inl x ->
                                        let is_return e =
                                          let uu____5715 =
                                            let uu____5716 =
                                              FStar_Syntax_Subst.compress e in
                                            uu____5716.FStar_Syntax_Syntax.n in
                                          match uu____5715 with
                                          | FStar_Syntax_Syntax.Tm_meta
                                              (e,FStar_Syntax_Syntax.Meta_monadic
                                               (uu____5721,uu____5722))
                                              ->
                                              let uu____5731 =
                                                let uu____5732 =
                                                  FStar_Syntax_Subst.compress
                                                    e in
                                                uu____5732.FStar_Syntax_Syntax.n in
                                              (match uu____5731 with
                                               | FStar_Syntax_Syntax.Tm_meta
                                                   (e,FStar_Syntax_Syntax.Meta_monadic_lift
                                                    (uu____5737,msrc,uu____5739))
                                                   when
                                                   FStar_Syntax_Util.is_pure_effect
                                                     msrc
                                                   ->
                                                   let uu____5748 =
                                                     FStar_Syntax_Subst.compress
                                                       e in
                                                   Some uu____5748
                                               | uu____5749 -> None)
                                          | uu____5750 -> None in
                                        let uu____5751 =
                                          is_return
                                            lb.FStar_Syntax_Syntax.lbdef in
                                        (match uu____5751 with
                                         | Some e ->
                                             let lb =
                                               let uu___159_5755 = lb in
                                               {
                                                 FStar_Syntax_Syntax.lbname =
                                                   (uu___159_5755.FStar_Syntax_Syntax.lbname);
                                                 FStar_Syntax_Syntax.lbunivs
                                                   =
                                                   (uu___159_5755.FStar_Syntax_Syntax.lbunivs);
                                                 FStar_Syntax_Syntax.lbtyp =
                                                   (uu___159_5755.FStar_Syntax_Syntax.lbtyp);
                                                 FStar_Syntax_Syntax.lbeff =
                                                   FStar_Syntax_Const.effect_PURE_lid;
                                                 FStar_Syntax_Syntax.lbdef =
                                                   e
                                               } in
                                             let uu____5756 =
                                               FStar_List.tl stack in
                                             let uu____5757 =
                                               let uu____5758 =
                                                 let uu____5761 =
                                                   let uu____5762 =
                                                     let uu____5770 =
                                                       FStar_Syntax_Util.mk_reify
                                                         body in
                                                     ((false, [lb]),
                                                       uu____5770) in
                                                   FStar_Syntax_Syntax.Tm_let
                                                     uu____5762 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____5761 in
                                               uu____5758 None
                                                 head.FStar_Syntax_Syntax.pos in
                                             norm cfg env uu____5756
                                               uu____5757
                                         | None  ->
                                             let uu____5787 =
                                               let uu____5788 =
                                                 is_return body in
                                               match uu____5788 with
                                               | Some
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       FStar_Syntax_Syntax.Tm_bvar
                                                       y;
                                                     FStar_Syntax_Syntax.tk =
                                                       uu____5791;
                                                     FStar_Syntax_Syntax.pos
                                                       = uu____5792;
                                                     FStar_Syntax_Syntax.vars
                                                       = uu____5793;_}
                                                   ->
                                                   FStar_Syntax_Syntax.bv_eq
                                                     x y
                                               | uu____5798 -> false in
                                             (match uu____5787 with
                                              | true  ->
                                                  norm cfg env stack
                                                    lb.FStar_Syntax_Syntax.lbdef
                                              | uu____5800 ->
                                                  let head =
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.mk_reify
                                                      lb.FStar_Syntax_Syntax.lbdef in
                                                  let body =
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.mk_reify
                                                      body in
                                                  let body =
                                                    let uu____5818 =
                                                      let uu____5821 =
                                                        let uu____5822 =
                                                          let uu____5837 =
                                                            let uu____5839 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                x in
                                                            [uu____5839] in
                                                          (uu____5837, body,
                                                            (Some
                                                               (FStar_Util.Inr
                                                                  (m, [])))) in
                                                        FStar_Syntax_Syntax.Tm_abs
                                                          uu____5822 in
                                                      FStar_Syntax_Syntax.mk
                                                        uu____5821 in
                                                    uu____5818 None
                                                      body.FStar_Syntax_Syntax.pos in
                                                  let bind_inst =
                                                    let uu____5869 =
                                                      let uu____5870 =
                                                        FStar_Syntax_Subst.compress
                                                          bind_repr in
                                                      uu____5870.FStar_Syntax_Syntax.n in
                                                    match uu____5869 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        (bind,uu____5876::uu____5877::[])
                                                        ->
                                                        let uu____5883 =
                                                          let uu____5886 =
                                                            let uu____5887 =
                                                              let uu____5892
                                                                =
                                                                let uu____5894
                                                                  =
                                                                  (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                    cfg.tcenv
                                                                    lb.FStar_Syntax_Syntax.lbtyp in
                                                                let uu____5895
                                                                  =
                                                                  let uu____5897
                                                                    =
                                                                    (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                    cfg.tcenv
                                                                    t in
                                                                  [uu____5897] in
                                                                uu____5894 ::
                                                                  uu____5895 in
                                                              (bind,
                                                                uu____5892) in
                                                            FStar_Syntax_Syntax.Tm_uinst
                                                              uu____5887 in
                                                          FStar_Syntax_Syntax.mk
                                                            uu____5886 in
                                                        uu____5883 None
                                                          t.FStar_Syntax_Syntax.pos
                                                    | uu____5909 ->
                                                        failwith
                                                          "NIY : Reification of indexed effects" in
                                                  let reified =
                                                    let uu____5915 =
                                                      let uu____5918 =
                                                        let uu____5919 =
                                                          let uu____5929 =
                                                            let uu____5931 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                lb.FStar_Syntax_Syntax.lbtyp in
                                                            let uu____5932 =
                                                              let uu____5934
                                                                =
                                                                FStar_Syntax_Syntax.as_arg
                                                                  t in
                                                              let uu____5935
                                                                =
                                                                let uu____5937
                                                                  =
                                                                  FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Syntax.tun in
                                                                let uu____5938
                                                                  =
                                                                  let uu____5940
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    head in
                                                                  let uu____5941
                                                                    =
                                                                    let uu____5943
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Syntax.tun in
                                                                    let uu____5944
                                                                    =
                                                                    let uu____5946
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    body in
                                                                    [uu____5946] in
                                                                    uu____5943
                                                                    ::
                                                                    uu____5944 in
                                                                  uu____5940
                                                                    ::
                                                                    uu____5941 in
                                                                uu____5937 ::
                                                                  uu____5938 in
                                                              uu____5934 ::
                                                                uu____5935 in
                                                            uu____5931 ::
                                                              uu____5932 in
                                                          (bind_inst,
                                                            uu____5929) in
                                                        FStar_Syntax_Syntax.Tm_app
                                                          uu____5919 in
                                                      FStar_Syntax_Syntax.mk
                                                        uu____5918 in
                                                    uu____5915 None
                                                      t.FStar_Syntax_Syntax.pos in
                                                  let uu____5958 =
                                                    FStar_List.tl stack in
                                                  norm cfg env uu____5958
                                                    reified))))
                          | FStar_Syntax_Syntax.Tm_app (head,args) ->
                              let ed =
                                FStar_TypeChecker_Env.get_effect_decl
                                  cfg.tcenv m in
                              let uu____5976 =
                                ed.FStar_Syntax_Syntax.bind_repr in
                              (match uu____5976 with
                               | (uu____5977,bind_repr) ->
                                   let maybe_unfold_action head =
                                     let maybe_extract_fv t =
                                       let t =
                                         let uu____6000 =
                                           let uu____6001 =
                                             FStar_Syntax_Subst.compress t in
                                           uu____6001.FStar_Syntax_Syntax.n in
                                         match uu____6000 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (t,uu____6007) -> t
                                         | uu____6012 -> head in
                                       let uu____6013 =
                                         let uu____6014 =
                                           FStar_Syntax_Subst.compress t in
                                         uu____6014.FStar_Syntax_Syntax.n in
                                       match uu____6013 with
                                       | FStar_Syntax_Syntax.Tm_fvar x ->
                                           Some x
                                       | uu____6019 -> None in
                                     let uu____6020 = maybe_extract_fv head in
                                     match uu____6020 with
                                     | Some x when
                                         let uu____6026 =
                                           FStar_Syntax_Syntax.lid_of_fv x in
                                         FStar_TypeChecker_Env.is_action
                                           cfg.tcenv uu____6026
                                         ->
                                         let head = norm cfg env [] head in
                                         let action_unfolded =
                                           let uu____6030 =
                                             maybe_extract_fv head in
                                           match uu____6030 with
                                           | Some uu____6033 -> Some true
                                           | uu____6034 -> Some false in
                                         (head, action_unfolded)
                                     | uu____6037 -> (head, None) in
                                   let rec bind_on_lift args acc =
                                     match args with
                                     | [] ->
                                         (match FStar_List.rev acc with
                                          | [] ->
                                              failwith
                                                "bind_on_lift should be always called with a non-empty list"
                                          | (head,uu____6084)::args ->
                                              let uu____6099 =
                                                maybe_unfold_action head in
                                              (match uu____6099 with
                                               | (head,found_action) ->
                                                   let mk tm =
                                                     (FStar_Syntax_Syntax.mk
                                                        tm) None
                                                       t.FStar_Syntax_Syntax.pos in
                                                   let body =
                                                     mk
                                                       (FStar_Syntax_Syntax.Tm_app
                                                          (head, args)) in
                                                   (match found_action with
                                                    | None  ->
                                                        FStar_Syntax_Util.mk_reify
                                                          body
                                                    | Some (false ) ->
                                                        mk
                                                          (FStar_Syntax_Syntax.Tm_meta
                                                             (body,
                                                               (FStar_Syntax_Syntax.Meta_monadic
                                                                  (m, t))))
                                                    | Some (true ) -> body)))
                                     | (e,q)::es ->
                                         let uu____6145 =
                                           let uu____6146 =
                                             FStar_Syntax_Subst.compress e in
                                           uu____6146.FStar_Syntax_Syntax.n in
                                         (match uu____6145 with
                                          | FStar_Syntax_Syntax.Tm_meta
                                              (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                               (m1,m2,t'))
                                              when
                                              Prims.op_Negation
                                                (FStar_Syntax_Util.is_pure_effect
                                                   m1)
                                              ->
                                              let x =
                                                FStar_Syntax_Syntax.gen_bv
                                                  "monadic_app_var" None t' in
                                              let body =
                                                let uu____6167 =
                                                  let uu____6173 =
                                                    let uu____6176 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        x in
                                                    (uu____6176, q) in
                                                  uu____6173 :: acc in
                                                bind_on_lift es uu____6167 in
                                              let lifted_e0 =
                                                reify_lift cfg.tcenv e0 m1 m2
                                                  t' in
                                              let continuation =
                                                FStar_Syntax_Util.abs
                                                  [(x, None)] body
                                                  (Some
                                                     (FStar_Util.Inr (m2, []))) in
                                              let bind_inst =
                                                let uu____6200 =
                                                  let uu____6201 =
                                                    FStar_Syntax_Subst.compress
                                                      bind_repr in
                                                  uu____6201.FStar_Syntax_Syntax.n in
                                                match uu____6200 with
                                                | FStar_Syntax_Syntax.Tm_uinst
                                                    (bind,uu____6207::uu____6208::[])
                                                    ->
                                                    let uu____6214 =
                                                      let uu____6217 =
                                                        let uu____6218 =
                                                          let uu____6223 =
                                                            let uu____6225 =
                                                              (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                cfg.tcenv t' in
                                                            let uu____6226 =
                                                              let uu____6228
                                                                =
                                                                (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                  cfg.tcenv t in
                                                              [uu____6228] in
                                                            uu____6225 ::
                                                              uu____6226 in
                                                          (bind, uu____6223) in
                                                        FStar_Syntax_Syntax.Tm_uinst
                                                          uu____6218 in
                                                      FStar_Syntax_Syntax.mk
                                                        uu____6217 in
                                                    uu____6214 None
                                                      e0.FStar_Syntax_Syntax.pos
                                                | uu____6240 ->
                                                    failwith
                                                      "NIY : Reification of indexed effects" in
                                              let uu____6243 =
                                                let uu____6246 =
                                                  let uu____6247 =
                                                    let uu____6257 =
                                                      let uu____6259 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          t' in
                                                      let uu____6260 =
                                                        let uu____6262 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            t in
                                                        let uu____6263 =
                                                          let uu____6265 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              FStar_Syntax_Syntax.tun in
                                                          let uu____6266 =
                                                            let uu____6268 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                lifted_e0 in
                                                            let uu____6269 =
                                                              let uu____6271
                                                                =
                                                                FStar_Syntax_Syntax.as_arg
                                                                  FStar_Syntax_Syntax.tun in
                                                              let uu____6272
                                                                =
                                                                let uu____6274
                                                                  =
                                                                  FStar_Syntax_Syntax.as_arg
                                                                    continuation in
                                                                [uu____6274] in
                                                              uu____6271 ::
                                                                uu____6272 in
                                                            uu____6268 ::
                                                              uu____6269 in
                                                          uu____6265 ::
                                                            uu____6266 in
                                                        uu____6262 ::
                                                          uu____6263 in
                                                      uu____6259 ::
                                                        uu____6260 in
                                                    (bind_inst, uu____6257) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____6247 in
                                                FStar_Syntax_Syntax.mk
                                                  uu____6246 in
                                              uu____6243 None
                                                e0.FStar_Syntax_Syntax.pos
                                          | FStar_Syntax_Syntax.Tm_meta
                                              (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                               uu____6287)
                                              ->
                                              bind_on_lift es ((e0, q) ::
                                                acc)
                                          | uu____6303 ->
                                              bind_on_lift es ((e, q) :: acc)) in
                                   let binded_head =
                                     let uu____6309 =
                                       let uu____6313 =
                                         FStar_Syntax_Syntax.as_arg head in
                                       uu____6313 :: args in
                                     bind_on_lift uu____6309 [] in
                                   let uu____6318 = FStar_List.tl stack in
                                   norm cfg env uu____6318 binded_head)
                          | FStar_Syntax_Syntax.Tm_meta
                              (e,FStar_Syntax_Syntax.Meta_monadic_lift
                               (msrc,mtgt,t'))
                              ->
                              let lifted =
                                reify_lift cfg.tcenv e msrc mtgt t' in
                              let uu____6332 = FStar_List.tl stack in
                              norm cfg env uu____6332 lifted
                          | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                              let branches =
                                FStar_All.pipe_right branches
                                  (FStar_List.map
                                     (fun uu____6415  ->
                                        match uu____6415 with
                                        | (pat,wopt,tm) ->
                                            let uu____6453 =
                                              FStar_Syntax_Util.mk_reify tm in
                                            (pat, wopt, uu____6453))) in
                              let tm =
                                mk
                                  (FStar_Syntax_Syntax.Tm_match (e, branches))
                                  t.FStar_Syntax_Syntax.pos in
                              let uu____6479 = FStar_List.tl stack in
                              norm cfg env uu____6479 tm
                          | uu____6480 -> norm cfg env stack head))
                | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
                    let should_reify =
                      match stack with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.tk = uu____6489;
                             FStar_Syntax_Syntax.pos = uu____6490;
                             FStar_Syntax_Syntax.vars = uu____6491;_},uu____6492,uu____6493))::uu____6494
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____6500 -> false in
                    (match should_reify with
                     | true  ->
                         let uu____6501 = FStar_List.tl stack in
                         let uu____6502 = reify_lift cfg.tcenv head m m' t in
                         norm cfg env uu____6501 uu____6502
                     | uu____6503 ->
                         let uu____6504 =
                           ((FStar_Syntax_Util.is_pure_effect m) ||
                              (FStar_Syntax_Util.is_ghost_effect m))
                             &&
                             (FStar_All.pipe_right cfg.steps
                                (FStar_List.contains
                                   PureSubtermsWithinComputations)) in
                         (match uu____6504 with
                          | true  ->
                              let stack =
                                (Steps ((cfg.steps), (cfg.delta_level))) ::
                                stack in
                              let cfg =
                                let uu___160_6509 = cfg in
                                {
                                  steps =
                                    [PureSubtermsWithinComputations;
                                    Primops;
                                    AllowUnboundUniverses;
                                    EraseUniverses;
                                    Exclude Zeta];
                                  tcenv = (uu___160_6509.tcenv);
                                  delta_level =
                                    [FStar_TypeChecker_Env.Inlining;
                                    FStar_TypeChecker_Env.Eager_unfolding_only]
                                } in
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m, m', t)),
                                      (head.FStar_Syntax_Syntax.pos))) ::
                                stack) head
                          | uu____6512 ->
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m, m', t)),
                                      (head.FStar_Syntax_Syntax.pos))) ::
                                stack) head))
                | uu____6515 ->
                    (match stack with
                     | uu____6516::uu____6517 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____6521)
                              -> norm cfg env ((Meta (m, r)) :: stack) head
                          | FStar_Syntax_Syntax.Meta_pattern args ->
                              let args = norm_pattern_args cfg env args in
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_pattern args),
                                      (t.FStar_Syntax_Syntax.pos))) :: stack)
                                head
                          | uu____6536 -> norm cfg env stack head)
                     | uu____6537 ->
                         let head = norm cfg env [] head in
                         let m =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               let uu____6547 =
                                 norm_pattern_args cfg env args in
                               FStar_Syntax_Syntax.Meta_pattern uu____6547
                           | uu____6554 -> m in
                         let t =
                           mk (FStar_Syntax_Syntax.Tm_meta (head, m))
                             t.FStar_Syntax_Syntax.pos in
                         rebuild cfg env stack t)))
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
            match FStar_Syntax_Util.is_pure_effect msrc with
            | true  ->
                let ed = FStar_TypeChecker_Env.get_effect_decl env mtgt in
                let uu____6568 = ed.FStar_Syntax_Syntax.return_repr in
                (match uu____6568 with
                 | (uu____6569,return_repr) ->
                     let return_inst =
                       let uu____6576 =
                         let uu____6577 =
                           FStar_Syntax_Subst.compress return_repr in
                         uu____6577.FStar_Syntax_Syntax.n in
                       match uu____6576 with
                       | FStar_Syntax_Syntax.Tm_uinst
                           (return_tm,uu____6583::[]) ->
                           let uu____6589 =
                             let uu____6592 =
                               let uu____6593 =
                                 let uu____6598 =
                                   let uu____6600 =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env t in
                                   [uu____6600] in
                                 (return_tm, uu____6598) in
                               FStar_Syntax_Syntax.Tm_uinst uu____6593 in
                             FStar_Syntax_Syntax.mk uu____6592 in
                           uu____6589 None e.FStar_Syntax_Syntax.pos
                       | uu____6612 ->
                           failwith "NIY : Reification of indexed effects" in
                     let uu____6615 =
                       let uu____6618 =
                         let uu____6619 =
                           let uu____6629 =
                             let uu____6631 = FStar_Syntax_Syntax.as_arg t in
                             let uu____6632 =
                               let uu____6634 = FStar_Syntax_Syntax.as_arg e in
                               [uu____6634] in
                             uu____6631 :: uu____6632 in
                           (return_inst, uu____6629) in
                         FStar_Syntax_Syntax.Tm_app uu____6619 in
                       FStar_Syntax_Syntax.mk uu____6618 in
                     uu____6615 None e.FStar_Syntax_Syntax.pos)
            | uu____6646 ->
                let uu____6647 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt in
                (match uu____6647 with
                 | None  ->
                     let uu____6649 =
                       FStar_Util.format2
                         "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                         (FStar_Ident.text_of_lid msrc)
                         (FStar_Ident.text_of_lid mtgt) in
                     failwith uu____6649
                 | Some
                     { FStar_TypeChecker_Env.msource = uu____6650;
                       FStar_TypeChecker_Env.mtarget = uu____6651;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____6652;
                           FStar_TypeChecker_Env.mlift_term = None ;_};_}
                     ->
                     failwith
                       "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                 | Some
                     { FStar_TypeChecker_Env.msource = uu____6663;
                       FStar_TypeChecker_Env.mtarget = uu____6664;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____6665;
                           FStar_TypeChecker_Env.mlift_term = Some lift;_};_}
                     ->
                     let uu____6683 = FStar_Syntax_Util.mk_reify e in
                     lift t FStar_Syntax_Syntax.tun uu____6683)
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
                (fun uu____6713  ->
                   match uu____6713 with
                   | (a,imp) ->
                       let uu____6720 = norm cfg env [] a in
                       (uu____6720, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp = ghost_to_pure_aux cfg env comp in
        match comp.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___161_6735 = comp in
            let uu____6738 =
              let uu____6739 =
                let uu____6745 = norm cfg env [] t in
                let uu____6746 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____6745, uu____6746) in
              FStar_Syntax_Syntax.Total uu____6739 in
            {
              FStar_Syntax_Syntax.n = uu____6738;
              FStar_Syntax_Syntax.tk = (uu___161_6735.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___161_6735.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___161_6735.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___162_6761 = comp in
            let uu____6764 =
              let uu____6765 =
                let uu____6771 = norm cfg env [] t in
                let uu____6772 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____6771, uu____6772) in
              FStar_Syntax_Syntax.GTotal uu____6765 in
            {
              FStar_Syntax_Syntax.n = uu____6764;
              FStar_Syntax_Syntax.tk = (uu___162_6761.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___162_6761.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___162_6761.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____6803  ->
                      match uu____6803 with
                      | (a,i) ->
                          let uu____6810 = norm cfg env [] a in
                          (uu____6810, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___131_6815  ->
                      match uu___131_6815 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____6819 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____6819
                      | f -> f)) in
            let uu___163_6823 = comp in
            let uu____6826 =
              let uu____6827 =
                let uu___164_6828 = ct in
                let uu____6829 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____6830 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____6833 = norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____6829;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___164_6828.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____6830;
                  FStar_Syntax_Syntax.effect_args = uu____6833;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____6827 in
            {
              FStar_Syntax_Syntax.n = uu____6826;
              FStar_Syntax_Syntax.tk = (uu___163_6823.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___163_6823.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___163_6823.FStar_Syntax_Syntax.vars)
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
        let norm t =
          norm
            (let uu___165_6850 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___165_6850.tcenv);
               delta_level = (uu___165_6850.delta_level)
             }) env [] t in
        let non_info t =
          let uu____6855 = norm t in
          FStar_Syntax_Util.non_informative uu____6855 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____6858 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___166_6872 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.tk = (uu___166_6872.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___166_6872.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___166_6872.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____6882 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            (match uu____6882 with
             | true  ->
                 let ct =
                   match downgrade_ghost_effect_name
                           ct.FStar_Syntax_Syntax.effect_name
                   with
                   | Some pure_eff ->
                       let uu___167_6887 = ct in
                       {
                         FStar_Syntax_Syntax.comp_univs =
                           (uu___167_6887.FStar_Syntax_Syntax.comp_univs);
                         FStar_Syntax_Syntax.effect_name = pure_eff;
                         FStar_Syntax_Syntax.result_typ =
                           (uu___167_6887.FStar_Syntax_Syntax.result_typ);
                         FStar_Syntax_Syntax.effect_args =
                           (uu___167_6887.FStar_Syntax_Syntax.effect_args);
                         FStar_Syntax_Syntax.flags =
                           (uu___167_6887.FStar_Syntax_Syntax.flags)
                       }
                   | None  ->
                       let ct =
                         FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv
                           c in
                       let uu___168_6889 = ct in
                       {
                         FStar_Syntax_Syntax.comp_univs =
                           (uu___168_6889.FStar_Syntax_Syntax.comp_univs);
                         FStar_Syntax_Syntax.effect_name =
                           FStar_Syntax_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.result_typ =
                           (uu___168_6889.FStar_Syntax_Syntax.result_typ);
                         FStar_Syntax_Syntax.effect_args =
                           (uu___168_6889.FStar_Syntax_Syntax.effect_args);
                         FStar_Syntax_Syntax.flags =
                           (uu___168_6889.FStar_Syntax_Syntax.flags)
                       } in
                 let uu___169_6890 = c in
                 {
                   FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct);
                   FStar_Syntax_Syntax.tk =
                     (uu___169_6890.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___169_6890.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___169_6890.FStar_Syntax_Syntax.vars)
                 }
             | uu____6895 -> c)
        | uu____6896 -> c
and norm_binder:
  cfg ->
    env ->
      FStar_Syntax_Syntax.binder ->
        (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  =
  fun cfg  ->
    fun env  ->
      fun uu____6899  ->
        match uu____6899 with
        | (x,imp) ->
            let uu____6902 =
              let uu___170_6903 = x in
              let uu____6904 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___170_6903.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___170_6903.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____6904
              } in
            (uu____6902, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____6910 =
          FStar_List.fold_left
            (fun uu____6917  ->
               fun b  ->
                 match uu____6917 with
                 | (nbs',env) ->
                     let b = norm_binder cfg env b in
                     ((b :: nbs'), (Dummy :: env))) ([], env) bs in
        match uu____6910 with | (nbs,uu____6934) -> FStar_List.rev nbs
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
            let uu____6951 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
            (match uu____6951 with
             | true  ->
                 let t = norm cfg env [] lc.FStar_Syntax_Syntax.res_typ in
                 let uu____6956 = FStar_Syntax_Util.is_total_lcomp lc in
                 (match uu____6956 with
                  | true  ->
                      let uu____6960 =
                        let uu____6963 =
                          let uu____6964 =
                            let uu____6967 = FStar_Syntax_Syntax.mk_Total t in
                            FStar_Syntax_Util.comp_set_flags uu____6967 flags in
                          FStar_Syntax_Util.lcomp_of_comp uu____6964 in
                        FStar_Util.Inl uu____6963 in
                      Some uu____6960
                  | uu____6970 ->
                      let uu____6971 =
                        let uu____6974 =
                          let uu____6975 =
                            let uu____6978 = FStar_Syntax_Syntax.mk_GTotal t in
                            FStar_Syntax_Util.comp_set_flags uu____6978 flags in
                          FStar_Syntax_Util.lcomp_of_comp uu____6975 in
                        FStar_Util.Inl uu____6974 in
                      Some uu____6971)
             | uu____6981 ->
                 Some
                   (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags)))
        | uu____6991 -> lopt
and rebuild:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          match stack with
          | [] -> t
          | (Debug tm)::stack ->
              ((let uu____7003 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                match uu____7003 with
                | true  ->
                    let uu____7004 = FStar_Syntax_Print.term_to_string tm in
                    let uu____7005 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print2 "Normalized %s to %s\n" uu____7004
                      uu____7005
                | uu____7006 -> ());
               rebuild cfg env stack t)
          | (Steps (s,dl))::stack ->
              rebuild
                (let uu___171_7013 = cfg in
                 { steps = s; tcenv = (uu___171_7013.tcenv); delta_level = dl
                 }) env stack t
          | (Meta (m,r))::stack ->
              let t = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack t
          | (MemoLazy r)::stack ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____7033  ->
                    let uu____7034 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____7034);
               rebuild cfg env stack t)
          | (Let (env',bs,lb,r))::stack ->
              let body = FStar_Syntax_Subst.close bs t in
              let t =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_let ((false, [lb]), body)) None r in
              rebuild cfg env' stack t
          | (Abs (env',bs,env'',lopt,r))::stack ->
              let bs = norm_binders cfg env' bs in
              let lopt = norm_lcomp_opt cfg env'' lopt in
              let uu____7071 =
                let uu___172_7072 = FStar_Syntax_Util.abs bs t lopt in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___172_7072.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___172_7072.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___172_7072.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack uu____7071
          | (Arg (Univ _,_,_))::_|(Arg (Dummy ,_,_))::_ ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack ->
              let t = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack t
          | (Arg (Clos (env,tm,m,uu____7094),aq,r))::stack ->
              (log cfg
                 (fun uu____7110  ->
                    let uu____7111 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____7111);
               (match FStar_List.contains (Exclude Iota) cfg.steps with
                | true  ->
                    (match FStar_List.contains WHNF cfg.steps with
                     | true  ->
                         let arg = closure_as_term cfg env tm in
                         let t =
                           FStar_Syntax_Syntax.extend_app t (arg, aq) None r in
                         rebuild cfg env stack t
                     | uu____7118 ->
                         let stack = (App (t, aq, r)) :: stack in
                         norm cfg env stack tm)
                | uu____7121 ->
                    let uu____7122 = FStar_ST.read m in
                    (match uu____7122 with
                     | None  ->
                         (match FStar_List.contains WHNF cfg.steps with
                          | true  ->
                              let arg = closure_as_term cfg env tm in
                              let t =
                                FStar_Syntax_Syntax.extend_app t (arg, aq)
                                  None r in
                              rebuild cfg env stack t
                          | uu____7142 ->
                              let stack = (MemoLazy m) :: (App (t, aq, r)) ::
                                stack in
                              norm cfg env stack tm)
                     | Some (uu____7148,a) ->
                         let t =
                           FStar_Syntax_Syntax.extend_app t (a, aq) None r in
                         rebuild cfg env stack t)))
          | (App (head,aq,r))::stack ->
              let t = FStar_Syntax_Syntax.extend_app head (t, aq) None r in
              let uu____7170 = maybe_simplify cfg.steps t in
              rebuild cfg env stack uu____7170
          | (Match (env,branches,r))::stack ->
              (log cfg
                 (fun uu____7177  ->
                    let uu____7178 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____7178);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____7183 =
                  let whnf = FStar_List.contains WHNF cfg.steps in
                  let cfg_exclude_iota_zeta =
                    let new_delta =
                      FStar_All.pipe_right cfg.delta_level
                        (FStar_List.filter
                           (fun uu___132_7190  ->
                              match uu___132_7190 with
                              | FStar_TypeChecker_Env.Inlining 
                                |FStar_TypeChecker_Env.Eager_unfolding_only 
                                  -> true
                              | uu____7191 -> false)) in
                    let steps' =
                      let uu____7194 =
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains PureSubtermsWithinComputations) in
                      match uu____7194 with
                      | true  -> [Exclude Zeta]
                      | uu____7196 -> [Exclude Iota; Exclude Zeta] in
                    let uu___173_7197 = cfg in
                    {
                      steps = (FStar_List.append steps' cfg.steps);
                      tcenv = (uu___173_7197.tcenv);
                      delta_level = new_delta
                    } in
                  let norm_or_whnf env t =
                    match whnf with
                    | true  -> closure_as_term cfg_exclude_iota_zeta env t
                    | uu____7207 -> norm cfg_exclude_iota_zeta env [] t in
                  let rec norm_pat env p =
                    match p.FStar_Syntax_Syntax.v with
                    | FStar_Syntax_Syntax.Pat_constant uu____7231 -> (p, env)
                    | FStar_Syntax_Syntax.Pat_disj [] ->
                        failwith "Impossible"
                    | FStar_Syntax_Syntax.Pat_disj (hd::tl) ->
                        let uu____7251 = norm_pat env hd in
                        (match uu____7251 with
                         | (hd,env') ->
                             let tl =
                               FStar_All.pipe_right tl
                                 (FStar_List.map
                                    (fun p  ->
                                       let uu____7287 = norm_pat env p in
                                       Prims.fst uu____7287)) in
                             ((let uu___174_7299 = p in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_disj (hd :: tl));
                                 FStar_Syntax_Syntax.ty =
                                   (uu___174_7299.FStar_Syntax_Syntax.ty);
                                 FStar_Syntax_Syntax.p =
                                   (uu___174_7299.FStar_Syntax_Syntax.p)
                               }), env'))
                    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                        let uu____7316 =
                          FStar_All.pipe_right pats
                            (FStar_List.fold_left
                               (fun uu____7350  ->
                                  fun uu____7351  ->
                                    match (uu____7350, uu____7351) with
                                    | ((pats,env),(p,b)) ->
                                        let uu____7416 = norm_pat env p in
                                        (match uu____7416 with
                                         | (p,env) -> (((p, b) :: pats), env)))
                               ([], env)) in
                        (match uu____7316 with
                         | (pats,env) ->
                             ((let uu___175_7482 = p in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_cons
                                      (fv, (FStar_List.rev pats)));
                                 FStar_Syntax_Syntax.ty =
                                   (uu___175_7482.FStar_Syntax_Syntax.ty);
                                 FStar_Syntax_Syntax.p =
                                   (uu___175_7482.FStar_Syntax_Syntax.p)
                               }), env))
                    | FStar_Syntax_Syntax.Pat_var x ->
                        let x =
                          let uu___176_7496 = x in
                          let uu____7497 =
                            norm_or_whnf env x.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___176_7496.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___176_7496.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____7497
                          } in
                        ((let uu___177_7503 = p in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_var x);
                            FStar_Syntax_Syntax.ty =
                              (uu___177_7503.FStar_Syntax_Syntax.ty);
                            FStar_Syntax_Syntax.p =
                              (uu___177_7503.FStar_Syntax_Syntax.p)
                          }), (Dummy :: env))
                    | FStar_Syntax_Syntax.Pat_wild x ->
                        let x =
                          let uu___178_7508 = x in
                          let uu____7509 =
                            norm_or_whnf env x.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___178_7508.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___178_7508.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____7509
                          } in
                        ((let uu___179_7515 = p in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_wild x);
                            FStar_Syntax_Syntax.ty =
                              (uu___179_7515.FStar_Syntax_Syntax.ty);
                            FStar_Syntax_Syntax.p =
                              (uu___179_7515.FStar_Syntax_Syntax.p)
                          }), (Dummy :: env))
                    | FStar_Syntax_Syntax.Pat_dot_term (x,t) ->
                        let x =
                          let uu___180_7525 = x in
                          let uu____7526 =
                            norm_or_whnf env x.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___180_7525.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___180_7525.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____7526
                          } in
                        let t = norm_or_whnf env t in
                        ((let uu___181_7533 = p in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_dot_term (x, t));
                            FStar_Syntax_Syntax.ty =
                              (uu___181_7533.FStar_Syntax_Syntax.ty);
                            FStar_Syntax_Syntax.p =
                              (uu___181_7533.FStar_Syntax_Syntax.p)
                          }), env) in
                  let branches =
                    match env with
                    | [] when whnf -> branches
                    | uu____7537 ->
                        FStar_All.pipe_right branches
                          (FStar_List.map
                             (fun branch  ->
                                let uu____7540 =
                                  FStar_Syntax_Subst.open_branch branch in
                                match uu____7540 with
                                | (p,wopt,e) ->
                                    let uu____7558 = norm_pat env p in
                                    (match uu____7558 with
                                     | (p,env) ->
                                         let wopt =
                                           match wopt with
                                           | None  -> None
                                           | Some w ->
                                               let uu____7582 =
                                                 norm_or_whnf env w in
                                               Some uu____7582 in
                                         let e = norm_or_whnf env e in
                                         FStar_Syntax_Util.branch
                                           (p, wopt, e)))) in
                  let uu____7587 =
                    mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches)) r in
                  rebuild cfg env stack uu____7587 in
                let rec is_cons head =
                  match head.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____7597) -> is_cons h
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
                  | uu____7608 -> false in
                let guard_when_clause wopt b rest =
                  match wopt with
                  | None  -> b
                  | Some w ->
                      let then_branch = b in
                      let else_branch =
                        mk (FStar_Syntax_Syntax.Tm_match (scrutinee, rest)) r in
                      FStar_Syntax_Util.if_then_else w then_branch
                        else_branch in
                let rec matches_pat scrutinee p =
                  let scrutinee = FStar_Syntax_Util.unmeta scrutinee in
                  let uu____7707 = FStar_Syntax_Util.head_and_args scrutinee in
                  match uu____7707 with
                  | (head,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_disj ps ->
                           let mopt =
                             FStar_Util.find_map ps
                               (fun p  ->
                                  let m = matches_pat scrutinee p in
                                  match m with
                                  | FStar_Util.Inl uu____7764 -> Some m
                                  | FStar_Util.Inr (true ) -> Some m
                                  | FStar_Util.Inr (false ) -> None) in
                           (match mopt with
                            | None  -> FStar_Util.Inr false
                            | Some m -> m)
                       | FStar_Syntax_Syntax.Pat_var _
                         |FStar_Syntax_Syntax.Pat_wild _ ->
                           FStar_Util.Inl [scrutinee]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____7795 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____7807 ->
                                let uu____7808 =
                                  let uu____7809 = is_cons head in
                                  Prims.op_Negation uu____7809 in
                                FStar_Util.Inr uu____7808)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____7823 =
                             let uu____7824 = FStar_Syntax_Util.un_uinst head in
                             uu____7824.FStar_Syntax_Syntax.n in
                           (match uu____7823 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____7831 ->
                                let uu____7832 =
                                  let uu____7833 = is_cons head in
                                  Prims.op_Negation uu____7833 in
                                FStar_Util.Inr uu____7832))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t,uu____7867)::rest_a,(p,uu____7870)::rest_p) ->
                      let uu____7898 = matches_pat t p in
                      (match uu____7898 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____7912 -> FStar_Util.Inr false in
                let rec matches scrutinee p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p,wopt,b)::rest ->
                      let uu____7983 = matches_pat scrutinee p in
                      (match uu____7983 with
                       | FStar_Util.Inr (false ) -> matches scrutinee rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____7993  ->
                                 let uu____7994 =
                                   FStar_Syntax_Print.pat_to_string p in
                                 let uu____7995 =
                                   let uu____7996 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____7996
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____7994 uu____7995);
                            (let env =
                               FStar_List.fold_left
                                 (fun env  ->
                                    fun t  ->
                                      let uu____8005 =
                                        let uu____8006 =
                                          let uu____8016 =
                                            FStar_Util.mk_ref (Some ([], t)) in
                                          ([], t, uu____8016, false) in
                                        Clos uu____8006 in
                                      uu____8005 :: env) env s in
                             let uu____8039 = guard_when_clause wopt b rest in
                             norm cfg env stack uu____8039))) in
                let uu____8040 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                match uu____8040 with
                | true  -> norm_and_rebuild_match ()
                | uu____8041 -> matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___133_8054  ->
                match uu___133_8054 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | uu____8057 -> [])) in
      let d =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____8061 -> d in
      { steps = s; tcenv = e; delta_level = d }
let normalize:
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun s  ->
    fun e  ->
      fun t  -> let uu____8072 = config s e in norm uu____8072 [] [] t
let normalize_comp:
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun s  ->
    fun e  ->
      fun t  -> let uu____8082 = config s e in norm_comp uu____8082 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  -> let uu____8089 = config [] env in norm_universe uu____8089 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun c  ->
      let uu____8096 = config [] env in ghost_to_pure_aux uu____8096 [] c
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
        let uu____8108 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____8108 in
      let uu____8109 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      match uu____8109 with
      | true  ->
          (match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
           with
           | Some pure_eff ->
               let uu___182_8111 = lc in
               {
                 FStar_Syntax_Syntax.eff_name = pure_eff;
                 FStar_Syntax_Syntax.res_typ =
                   (uu___182_8111.FStar_Syntax_Syntax.res_typ);
                 FStar_Syntax_Syntax.cflags =
                   (uu___182_8111.FStar_Syntax_Syntax.cflags);
                 FStar_Syntax_Syntax.comp =
                   ((fun uu____8112  ->
                       let uu____8113 = lc.FStar_Syntax_Syntax.comp () in
                       ghost_to_pure env uu____8113))
               }
           | None  -> lc)
      | uu____8114 -> lc
let term_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun env  ->
    fun t  ->
      let uu____8121 = normalize [AllowUnboundUniverses] env t in
      FStar_Syntax_Print.term_to_string uu____8121
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let uu____8128 =
        let uu____8129 = config [AllowUnboundUniverses] env in
        norm_comp uu____8129 [] c in
      FStar_Syntax_Print.comp_to_string uu____8128
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
        let rec aux t =
          let t = FStar_Syntax_Subst.compress t in
          match t.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              let t0 = aux x.FStar_Syntax_Syntax.sort in
              (match t0.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_refine (y,phi1) ->
                   let uu____8166 =
                     let uu____8167 =
                       let uu____8172 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____8172) in
                     FStar_Syntax_Syntax.Tm_refine uu____8167 in
                   mk uu____8166 t0.FStar_Syntax_Syntax.pos
               | uu____8177 -> t)
          | uu____8178 -> t in
        aux t
let eta_expand_with_type:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun t  ->
    fun sort  ->
      let uu____8185 = FStar_Syntax_Util.arrow_formals_comp sort in
      match uu____8185 with
      | (binders,c) ->
          (match binders with
           | [] -> t
           | uu____8201 ->
               let uu____8205 =
                 FStar_All.pipe_right binders
                   FStar_Syntax_Util.args_of_binders in
               (match uu____8205 with
                | (binders,args) ->
                    let uu____8215 =
                      (FStar_Syntax_Syntax.mk_Tm_app t args) None
                        t.FStar_Syntax_Syntax.pos in
                    let uu____8220 =
                      let uu____8227 =
                        FStar_All.pipe_right
                          (FStar_Syntax_Util.lcomp_of_comp c)
                          (fun _0_39  -> FStar_Util.Inl _0_39) in
                      FStar_All.pipe_right uu____8227
                        (fun _0_40  -> Some _0_40) in
                    FStar_Syntax_Util.abs binders uu____8215 uu____8220))
let eta_expand:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun t  ->
      let uu____8263 =
        let uu____8267 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
        (uu____8267, (t.FStar_Syntax_Syntax.n)) in
      match uu____8263 with
      | (Some sort,uu____8274) ->
          let uu____8276 = mk sort t.FStar_Syntax_Syntax.pos in
          eta_expand_with_type t uu____8276
      | (uu____8277,FStar_Syntax_Syntax.Tm_name x) ->
          eta_expand_with_type t x.FStar_Syntax_Syntax.sort
      | uu____8281 ->
          let uu____8285 = FStar_Syntax_Util.head_and_args t in
          (match uu____8285 with
           | (head,args) ->
               let uu____8311 =
                 let uu____8312 = FStar_Syntax_Subst.compress head in
                 uu____8312.FStar_Syntax_Syntax.n in
               (match uu____8311 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____8315,thead) ->
                    let uu____8329 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____8329 with
                     | (formals,tres) ->
                         (match (FStar_List.length formals) =
                                  (FStar_List.length args)
                          with
                          | true  -> t
                          | uu____8359 ->
                              let uu____8360 =
                                env.FStar_TypeChecker_Env.type_of
                                  (let uu___183_8364 = env in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___183_8364.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___183_8364.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___183_8364.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___183_8364.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___183_8364.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___183_8364.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       None;
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___183_8364.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___183_8364.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___183_8364.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___183_8364.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___183_8364.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___183_8364.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___183_8364.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___183_8364.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___183_8364.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___183_8364.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___183_8364.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___183_8364.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___183_8364.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___183_8364.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       true;
                                     FStar_TypeChecker_Env.qname_and_index =
                                       (uu___183_8364.FStar_TypeChecker_Env.qname_and_index)
                                   }) t in
                              (match uu____8360 with
                               | (uu____8365,ty,uu____8367) ->
                                   eta_expand_with_type t ty)))
                | uu____8368 ->
                    let uu____8369 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___184_8373 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___184_8373.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___184_8373.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___184_8373.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___184_8373.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___184_8373.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___184_8373.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ = None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___184_8373.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___184_8373.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___184_8373.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___184_8373.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___184_8373.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___184_8373.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___184_8373.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___184_8373.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___184_8373.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___184_8373.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___184_8373.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___184_8373.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___184_8373.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___184_8373.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___184_8373.FStar_TypeChecker_Env.qname_and_index)
                         }) t in
                    (match uu____8369 with
                     | (uu____8374,ty,uu____8376) ->
                         eta_expand_with_type t ty)))