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
type primitive_step =
  {
  name: FStar_Ident.lid;
  arity: Prims.int;
  strong_reduction_ok: Prims.bool;
  interpretation:
    FStar_Range.range ->
      FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term Prims.option;}
type closure =
  | Clos of (closure Prims.list* FStar_Syntax_Syntax.term* (closure
  Prims.list* FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo*
  Prims.bool)
  | Univ of FStar_Syntax_Syntax.universe
  | Dummy
let uu___is_Clos: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Clos _0 -> true | uu____165 -> false
let __proj__Clos__item___0:
  closure ->
    (closure Prims.list* FStar_Syntax_Syntax.term* (closure Prims.list*
      FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo* Prims.bool)
  = fun projectee  -> match projectee with | Clos _0 -> _0
let uu___is_Univ: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____204 -> false
let __proj__Univ__item___0: closure -> FStar_Syntax_Syntax.universe =
  fun projectee  -> match projectee with | Univ _0 -> _0
let uu___is_Dummy: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____215 -> false
type env = closure Prims.list
let closure_to_string: closure -> Prims.string =
  fun uu___132_219  ->
    match uu___132_219 with
    | Clos (uu____220,t,uu____222,uu____223) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____234 -> "Univ"
    | Dummy  -> "dummy"
type cfg =
  {
  steps: steps;
  tcenv: FStar_TypeChecker_Env.env;
  delta_level: FStar_TypeChecker_Env.delta_level Prims.list;
  primitive_steps: primitive_step Prims.list;}
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
  | Steps of (steps* primitive_step Prims.list*
  FStar_TypeChecker_Env.delta_level Prims.list)
  | Debug of FStar_Syntax_Syntax.term
let uu___is_Arg: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Arg _0 -> true | uu____347 -> false
let __proj__Arg__item___0:
  stack_elt -> (closure* FStar_Syntax_Syntax.aqual* FStar_Range.range) =
  fun projectee  -> match projectee with | Arg _0 -> _0
let uu___is_UnivArgs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____371 -> false
let __proj__UnivArgs__item___0:
  stack_elt -> (FStar_Syntax_Syntax.universe Prims.list* FStar_Range.range) =
  fun projectee  -> match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____395 -> false
let __proj__MemoLazy__item___0:
  stack_elt -> (env* FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo =
  fun projectee  -> match projectee with | MemoLazy _0 -> _0
let uu___is_Match: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____422 -> false
let __proj__Match__item___0: stack_elt -> (env* branches* FStar_Range.range)
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Abs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____451 -> false
let __proj__Abs__item___0:
  stack_elt ->
    (env* FStar_Syntax_Syntax.binders* env*
      (FStar_Syntax_Syntax.lcomp,FStar_Syntax_Syntax.residual_comp)
      FStar_Util.either Prims.option* FStar_Range.range)
  = fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____490 -> false
let __proj__App__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.aqual* FStar_Range.range)
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Meta: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____513 -> false
let __proj__Meta__item___0:
  stack_elt -> (FStar_Syntax_Syntax.metadata* FStar_Range.range) =
  fun projectee  -> match projectee with | Meta _0 -> _0
let uu___is_Let: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____535 -> false
let __proj__Let__item___0:
  stack_elt ->
    (env* FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.letbinding*
      FStar_Range.range)
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Steps: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Steps _0 -> true | uu____564 -> false
let __proj__Steps__item___0:
  stack_elt ->
    (steps* primitive_step Prims.list* FStar_TypeChecker_Env.delta_level
      Prims.list)
  = fun projectee  -> match projectee with | Steps _0 -> _0
let uu___is_Debug: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____591 -> false
let __proj__Debug__item___0: stack_elt -> FStar_Syntax_Syntax.term =
  fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list
let mk t r = FStar_Syntax_Syntax.mk t None r
let set_memo r t =
  let uu____639 = FStar_ST.read r in
  match uu____639 with
  | Some uu____644 -> failwith "Unexpected set_memo: thunk already evaluated"
  | None  -> FStar_ST.write r (Some t)
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____653 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____653 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___133_658  ->
    match uu___133_658 with
    | Arg (c,uu____660,uu____661) ->
        let uu____662 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____662
    | MemoLazy uu____663 -> "MemoLazy"
    | Abs (uu____667,bs,uu____669,uu____670,uu____671) ->
        let uu____678 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____678
    | UnivArgs uu____683 -> "UnivArgs"
    | Match uu____687 -> "Match"
    | App (t,uu____692,uu____693) ->
        let uu____694 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____694
    | Meta (m,uu____696) -> "Meta"
    | Let uu____697 -> "Let"
    | Steps (uu____702,uu____703,uu____704) -> "Steps"
    | Debug t ->
        let uu____710 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____710
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____716 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____716 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____730 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____730 then f () else ()
let is_empty uu___134_739 =
  match uu___134_739 with | [] -> true | uu____741 -> false
let lookup_bvar env x =
  try FStar_List.nth env x.FStar_Syntax_Syntax.index
  with
  | uu____759 ->
      let uu____760 =
        let uu____761 = FStar_Syntax_Print.db_to_string x in
        FStar_Util.format1 "Failed to find %s\n" uu____761 in
      failwith uu____760
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
          let uu____792 =
            FStar_List.fold_left
              (fun uu____801  ->
                 fun u1  ->
                   match uu____801 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____816 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____816 with
                        | (k_u,n1) ->
                            let uu____825 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____825
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____792 with
          | (uu____835,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____851 = FStar_List.nth env x in
                 match uu____851 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____854 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____858 ->
                   let uu____859 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____859
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_zero 
            |FStar_Syntax_Syntax.U_unif _
             |FStar_Syntax_Syntax.U_name _|FStar_Syntax_Syntax.U_unknown  ->
              [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____869 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____869 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____880 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____880 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____885 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____888 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____888 with
                                  | (uu____891,m) -> n1 <= m)) in
                        if uu____885 then rest1 else us1
                    | uu____895 -> us1)
               | uu____898 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____901 = aux u3 in
              FStar_List.map (fun _0_29  -> FStar_Syntax_Syntax.U_succ _0_29)
                uu____901 in
        let uu____903 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____903
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____905 = aux u in
           match uu____905 with
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
          (fun uu____1002  ->
             let uu____1003 = FStar_Syntax_Print.tag_of_term t in
             let uu____1004 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1003
               uu____1004);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1005 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1008 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown 
                |FStar_Syntax_Syntax.Tm_constant _
                 |FStar_Syntax_Syntax.Tm_name _|FStar_Syntax_Syntax.Tm_fvar _
                  -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____1032 -> t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____1042 =
                    let uu____1043 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____1043 in
                  mk uu____1042 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t2,us) ->
                  let uu____1050 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t2 uu____1050
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____1052 = lookup_bvar env x in
                  (match uu____1052 with
                   | Univ uu____1053 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____1057) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____1125 = closures_as_binders_delayed cfg env bs in
                  (match uu____1125 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____1145 =
                         let uu____1146 =
                           let uu____1161 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____1161) in
                         FStar_Syntax_Syntax.Tm_abs uu____1146 in
                       mk uu____1145 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____1191 = closures_as_binders_delayed cfg env bs in
                  (match uu____1191 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____1222 =
                    let uu____1229 =
                      let uu____1233 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____1233] in
                    closures_as_binders_delayed cfg env uu____1229 in
                  (match uu____1222 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____1247 =
                         let uu____1248 =
                           let uu____1253 =
                             let uu____1254 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____1254 Prims.fst in
                           (uu____1253, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____1248 in
                       mk uu____1247 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____1322 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____1322
                    | FStar_Util.Inr c ->
                        let uu____1336 = close_comp cfg env c in
                        FStar_Util.Inr uu____1336 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____1351 =
                    let uu____1352 =
                      let uu____1370 = closure_as_term_delayed cfg env t11 in
                      (uu____1370, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____1352 in
                  mk uu____1351 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____1408 =
                    let uu____1409 =
                      let uu____1414 = closure_as_term_delayed cfg env t' in
                      let uu____1417 =
                        let uu____1418 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____1418 in
                      (uu____1414, uu____1417) in
                    FStar_Syntax_Syntax.Tm_meta uu____1409 in
                  mk uu____1408 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____1460 =
                    let uu____1461 =
                      let uu____1466 = closure_as_term_delayed cfg env t' in
                      let uu____1469 =
                        let uu____1470 =
                          let uu____1475 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____1475) in
                        FStar_Syntax_Syntax.Meta_monadic uu____1470 in
                      (uu____1466, uu____1469) in
                    FStar_Syntax_Syntax.Tm_meta uu____1461 in
                  mk uu____1460 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____1494 =
                    let uu____1495 =
                      let uu____1500 = closure_as_term_delayed cfg env t' in
                      let uu____1503 =
                        let uu____1504 =
                          let uu____1510 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____1510) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____1504 in
                      (uu____1500, uu____1503) in
                    FStar_Syntax_Syntax.Tm_meta uu____1495 in
                  mk uu____1494 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____1523 =
                    let uu____1524 =
                      let uu____1529 = closure_as_term_delayed cfg env t' in
                      (uu____1529, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____1524 in
                  mk uu____1523 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____1550  -> Dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let body1 =
                    match lb.FStar_Syntax_Syntax.lbname with
                    | FStar_Util.Inr uu____1561 -> body
                    | FStar_Util.Inl uu____1562 ->
                        closure_as_term cfg (Dummy :: env0) body in
                  let lb1 =
                    let uu___147_1564 = lb in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___147_1564.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___147_1564.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = typ;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___147_1564.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = def
                    } in
                  mk (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((uu____1571,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____1595  -> fun env2  -> Dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____1600 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____1600
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____1604  -> fun env2  -> Dummy :: env2) lbs
                          env_univs in
                    let uu___148_1607 = lb in
                    let uu____1608 =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let uu____1611 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___148_1607.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___148_1607.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = uu____1608;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___148_1607.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____1611
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____1622  -> fun env1  -> Dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____1677 =
                    match uu____1677 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____1723 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_disj [] ->
                              failwith "Impossible"
                          | FStar_Syntax_Syntax.Pat_disj (hd1::tl1) ->
                              let uu____1743 = norm_pat env2 hd1 in
                              (match uu____1743 with
                               | (hd2,env') ->
                                   let tl2 =
                                     FStar_All.pipe_right tl1
                                       (FStar_List.map
                                          (fun p1  ->
                                             let uu____1779 =
                                               norm_pat env2 p1 in
                                             Prims.fst uu____1779)) in
                                   ((let uu___149_1791 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_disj (hd2
                                            :: tl2));
                                       FStar_Syntax_Syntax.ty =
                                         (uu___149_1791.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___149_1791.FStar_Syntax_Syntax.p)
                                     }), env'))
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____1808 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____1842  ->
                                        fun uu____1843  ->
                                          match (uu____1842, uu____1843) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____1908 =
                                                norm_pat env3 p1 in
                                              (match uu____1908 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____1808 with
                               | (pats1,env3) ->
                                   ((let uu___150_1974 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.ty =
                                         (uu___150_1974.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___150_1974.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___151_1988 = x in
                                let uu____1989 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___151_1988.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___151_1988.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1989
                                } in
                              ((let uu___152_1995 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___152_1995.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___152_1995.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___153_2000 = x in
                                let uu____2001 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___153_2000.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___153_2000.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____2001
                                } in
                              ((let uu___154_2007 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___154_2007.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___154_2007.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___155_2017 = x in
                                let uu____2018 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___155_2017.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___155_2017.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____2018
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___156_2025 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___156_2025.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___156_2025.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____2028 = norm_pat env1 pat in
                        (match uu____2028 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | None  -> None
                               | Some w ->
                                   let uu____2052 =
                                     closure_as_term cfg env2 w in
                                   Some uu____2052 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____2057 =
                    let uu____2058 =
                      let uu____2074 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____2074) in
                    FStar_Syntax_Syntax.Tm_match uu____2058 in
                  mk uu____2057 t1.FStar_Syntax_Syntax.pos))
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
        | uu____2127 -> closure_as_term cfg env t
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
        | uu____2143 ->
            FStar_List.map
              (fun uu____2153  ->
                 match uu____2153 with
                 | (x,imp) ->
                     let uu____2168 = closure_as_term_delayed cfg env x in
                     (uu____2168, imp)) args
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
        let uu____2180 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____2204  ->
                  fun uu____2205  ->
                    match (uu____2204, uu____2205) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___157_2249 = b in
                          let uu____2250 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___157_2249.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___157_2249.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____2250
                          } in
                        let env2 = Dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____2180 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____2297 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____2309 = closure_as_term_delayed cfg env t in
                 let uu____2310 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____2309 uu____2310
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____2320 = closure_as_term_delayed cfg env t in
                 let uu____2321 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____2320 uu____2321
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
                        (fun uu___135_2337  ->
                           match uu___135_2337 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____2341 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____2341
                           | f -> f)) in
                 let uu____2345 =
                   let uu___158_2346 = c1 in
                   let uu____2347 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____2347;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___158_2346.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____2345)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.cflags Prims.list =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_List.filter
         (fun uu___136_2351  ->
            match uu___136_2351 with
            | FStar_Syntax_Syntax.DECREASES uu____2352 -> false
            | uu____2355 -> true))
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
            let uu____2383 = FStar_Syntax_Util.is_total_lcomp lc in
            if uu____2383
            then
              Some
                (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, flags))
            else
              (let uu____2400 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
               if uu____2400
               then
                 Some
                   (FStar_Util.Inr
                      (FStar_Syntax_Const.effect_GTot_lid, flags))
               else
                 Some
                   (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags)))
        | uu____2426 -> lopt
let built_in_primitive_steps: primitive_step Prims.list =
  let const_as_tm c p = mk (FStar_Syntax_Syntax.Tm_constant c) p in
  let int_as_const p i =
    let uu____2450 =
      let uu____2451 =
        let uu____2457 = FStar_Util.string_of_int i in (uu____2457, None) in
      FStar_Const.Const_int uu____2451 in
    const_as_tm uu____2450 p in
  let bool_as_const p b = const_as_tm (FStar_Const.Const_bool b) p in
  let string_as_const p b =
    const_as_tm
      (FStar_Const.Const_string ((FStar_Util.bytes_of_string b), p)) p in
  let arg_as_int uu____2484 =
    match uu____2484 with
    | (a,uu____2489) ->
        let uu____2491 =
          let uu____2492 = FStar_Syntax_Subst.compress a in
          uu____2492.FStar_Syntax_Syntax.n in
        (match uu____2491 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i,None ))
             ->
             let uu____2502 = FStar_Util.int_of_string i in Some uu____2502
         | uu____2503 -> None) in
  let arg_as_bounded_int uu____2510 =
    match uu____2510 with
    | (a,uu____2515) ->
        let uu____2517 =
          let uu____2518 = FStar_Syntax_Subst.compress a in
          uu____2518.FStar_Syntax_Syntax.n in
        (match uu____2517 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.tk = uu____2523;
                FStar_Syntax_Syntax.pos = uu____2524;
                FStar_Syntax_Syntax.vars = uu____2525;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,None ));
                                                            FStar_Syntax_Syntax.tk
                                                              = uu____2527;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____2528;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____2529;_},uu____2530)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____2561 = FStar_Util.int_of_string i in Some uu____2561
         | uu____2562 -> None) in
  let arg_as_bool uu____2569 =
    match uu____2569 with
    | (a,uu____2574) ->
        let uu____2576 =
          let uu____2577 = FStar_Syntax_Subst.compress a in
          uu____2577.FStar_Syntax_Syntax.n in
        (match uu____2576 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
             Some b
         | uu____2582 -> None) in
  let arg_as_string uu____2589 =
    match uu____2589 with
    | (a,uu____2594) ->
        let uu____2596 =
          let uu____2597 = FStar_Syntax_Subst.compress a in
          uu____2597.FStar_Syntax_Syntax.n in
        (match uu____2596 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (bytes,uu____2602)) -> Some (FStar_Util.string_of_bytes bytes)
         | uu____2605 -> None) in
  let lift_unary f aopts =
    match aopts with
    | (Some a)::[] -> let uu____2635 = f a in Some uu____2635
    | uu____2636 -> None in
  let lift_binary f aopts =
    match aopts with
    | (Some a0)::(Some a1)::[] -> let uu____2675 = f a0 a1 in Some uu____2675
    | uu____2676 -> None in
  let unary_op as_a f r args =
    let uu____2720 = FStar_List.map as_a args in lift_unary (f r) uu____2720 in
  let binary_op as_a f r args =
    let uu____2770 = FStar_List.map as_a args in lift_binary (f r) uu____2770 in
  let as_primitive_step uu____2787 =
    match uu____2787 with
    | (l,arity,f) ->
        { name = l; arity; strong_reduction_ok = true; interpretation = f } in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  -> fun x  -> let uu____2825 = f x in int_as_const r uu____2825) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2848 = f x y in int_as_const r uu____2848) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  -> fun x  -> let uu____2865 = f x in bool_as_const r uu____2865) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2888 = f x y in bool_as_const r uu____2888) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2911 = f x y in string_as_const r uu____2911) in
  let list_of_string1 rng s =
    let mk1 x = mk x rng in
    let name l =
      let uu____2931 =
        let uu____2932 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            None in
        FStar_Syntax_Syntax.Tm_fvar uu____2932 in
      mk1 uu____2931 in
    let ctor l =
      let uu____2939 =
        let uu____2940 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            (Some FStar_Syntax_Syntax.Data_ctor) in
        FStar_Syntax_Syntax.Tm_fvar uu____2940 in
      mk1 uu____2939 in
    let char_t = name FStar_Syntax_Const.char_lid in
    let nil_char =
      let uu____2947 =
        let uu____2948 =
          let uu____2949 = ctor FStar_Syntax_Const.nil_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____2949
            [FStar_Syntax_Syntax.U_zero] in
        let uu____2950 =
          let uu____2951 = FStar_Syntax_Syntax.iarg char_t in [uu____2951] in
        FStar_Syntax_Syntax.mk_Tm_app uu____2948 uu____2950 in
      uu____2947 None rng in
    let uu____2956 = FStar_String.list_of_string s in
    FStar_List.fold_right
      (fun c  ->
         fun a  ->
           let uu____2962 =
             let uu____2963 =
               let uu____2964 = ctor FStar_Syntax_Const.cons_lid in
               FStar_Syntax_Syntax.mk_Tm_uinst uu____2964
                 [FStar_Syntax_Syntax.U_zero] in
             let uu____2965 =
               let uu____2966 = FStar_Syntax_Syntax.iarg char_t in
               let uu____2967 =
                 let uu____2969 =
                   let uu____2970 =
                     mk1
                       (FStar_Syntax_Syntax.Tm_constant
                          (FStar_Const.Const_char c)) in
                   FStar_Syntax_Syntax.as_arg uu____2970 in
                 let uu____2971 =
                   let uu____2973 = FStar_Syntax_Syntax.as_arg a in
                   [uu____2973] in
                 uu____2969 :: uu____2971 in
               uu____2966 :: uu____2967 in
             FStar_Syntax_Syntax.mk_Tm_app uu____2963 uu____2965 in
           uu____2962 None rng) uu____2956 nil_char in
  let string_of_int1 rng i =
    let uu____2985 = FStar_Util.string_of_int i in
    string_as_const rng uu____2985 in
  let string_of_bool1 rng b =
    string_as_const rng (if b then "true" else "false") in
  let basic_ops =
    let uu____3004 =
      let uu____3014 =
        let uu____3024 =
          let uu____3034 =
            let uu____3044 =
              let uu____3054 =
                let uu____3064 =
                  let uu____3074 =
                    let uu____3084 =
                      let uu____3094 =
                        let uu____3104 =
                          let uu____3114 =
                            let uu____3124 =
                              let uu____3134 =
                                let uu____3144 =
                                  let uu____3154 =
                                    let uu____3164 =
                                      let uu____3173 =
                                        FStar_Syntax_Const.p2l
                                          ["FStar";
                                          "String";
                                          "list_of_string"] in
                                      (uu____3173, (Prims.parse_int "1"),
                                        (unary_op arg_as_string
                                           list_of_string1)) in
                                    [uu____3164] in
                                  (FStar_Syntax_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_bool string_of_bool1))
                                    :: uu____3154 in
                                (FStar_Syntax_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (unary_op arg_as_int string_of_int1)) ::
                                  uu____3144 in
                              (FStar_Syntax_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____3134 in
                            (FStar_Syntax_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____3124 in
                          (FStar_Syntax_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____3114 in
                        (FStar_Syntax_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____3104 in
                      (FStar_Syntax_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____3094 in
                    (FStar_Syntax_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
                      :: uu____3084 in
                  (FStar_Syntax_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____3074 in
                (FStar_Syntax_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____3064 in
              (FStar_Syntax_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____3054 in
            (FStar_Syntax_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____3044 in
          (FStar_Syntax_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____3034 in
        (FStar_Syntax_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____3024 in
      (FStar_Syntax_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____3014 in
    (FStar_Syntax_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____3004 in
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
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____3464 =
              let uu____3473 = FStar_Syntax_Const.p2l ["FStar"; m; "add"] in
              (uu____3473, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  -> fun x  -> fun y  -> int_as_const r (x + y)))) in
            let uu____3482 =
              let uu____3492 =
                let uu____3501 = FStar_Syntax_Const.p2l ["FStar"; m; "sub"] in
                (uu____3501, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  -> fun x  -> fun y  -> int_as_const r (x - y)))) in
              let uu____3510 =
                let uu____3520 =
                  let uu____3529 = FStar_Syntax_Const.p2l ["FStar"; m; "mul"] in
                  (uu____3529, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  -> fun x  -> fun y  -> int_as_const r (x * y)))) in
                [uu____3520] in
              uu____3492 :: uu____3510 in
            uu____3464 :: uu____3482)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_bool rng args =
    match args with
    | (_typ,uu____3598)::(a1,uu____3600)::(a2,uu____3602)::[] ->
        let uu____3631 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3631 with
         | FStar_Syntax_Util.Equal  ->
             let uu____3633 =
               mk
                 (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_bool true)) rng in
             Some uu____3633
         | FStar_Syntax_Util.NotEqual  ->
             let uu____3638 =
               mk
                 (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_bool false)) rng in
             Some uu____3638
         | uu____3643 -> None)
    | uu____3644 -> failwith "Unexpected number of arguments" in
  let interp_prop r args =
    match args with
    | (_typ,_)::(a1,_)::(a2,_)::[]|(_typ,_)::_::(a1,_)::(a2,_)::[] ->
        let uu____3726 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3726 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___159_3730 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___159_3730.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___159_3730.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___159_3730.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___160_3737 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___160_3737.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___160_3737.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___160_3737.FStar_Syntax_Syntax.vars)
                })
         | uu____3742 -> None)
    | uu____3743 -> failwith "Unexpected number of arguments" in
  let decidable_equality =
    {
      name = FStar_Syntax_Const.op_Eq;
      arity = (Prims.parse_int "3");
      strong_reduction_ok = true;
      interpretation = interp_bool
    } in
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
  [decidable_equality; propositional_equality; hetero_propositional_equality]
let reduce_primops:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      let uu____3754 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops cfg.steps) in
      if uu____3754
      then tm
      else
        (let uu____3756 = FStar_Syntax_Util.head_and_args tm in
         match uu____3756 with
         | (head1,args) ->
             let uu____3782 =
               let uu____3783 = FStar_Syntax_Util.un_uinst head1 in
               uu____3783.FStar_Syntax_Syntax.n in
             (match uu____3782 with
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____3787 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps in
                  (match uu____3787 with
                   | None  -> tm
                   | Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then tm
                       else
                         (let uu____3799 =
                            prim_step.interpretation
                              head1.FStar_Syntax_Syntax.pos args in
                          match uu____3799 with
                          | None  -> tm
                          | Some reduced -> reduced))
              | uu____3802 -> tm))
let reduce_equality:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___161_3809 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___161_3809.tcenv);
           delta_level = (uu___161_3809.delta_level);
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
        let uu___162_3831 = t in
        {
          FStar_Syntax_Syntax.n = (uu___162_3831.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___162_3831.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___162_3831.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid ->
            Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid ->
            Some false
        | uu____3850 -> None in
      let simplify arg = ((simp_t (Prims.fst arg)), arg) in
      let uu____3877 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps) in
      if uu____3877
      then reduce_primops cfg tm
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
             let uu____3917 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____3917
             then
               let uu____3918 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____3918 with
                | (Some (true ),_)::(_,(arg,_))::[]
                  |(_,(arg,_))::(Some (true ),_)::[] -> arg
                | (Some (false ),_)::_::[]|_::(Some (false ),_)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4084 -> tm)
             else
               (let uu____4094 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____4094
                then
                  let uu____4095 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____4095 with
                  | (Some (true ),_)::_::[]|_::(Some (true ),_)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),_)::(_,(arg,_))::[]
                    |(_,(arg,_))::(Some (false ),_)::[] -> arg
                  | uu____4261 -> tm
                else
                  (let uu____4271 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____4271
                   then
                     let uu____4272 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____4272 with
                     | _::(Some (true ),_)::[]|(Some (false ),_)::_::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____4361)::(uu____4362,(arg,uu____4364))::[]
                         -> arg
                     | uu____4405 -> tm
                   else
                     (let uu____4415 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____4415
                      then
                        let uu____4416 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____4416 with
                        | (Some (true ),uu____4449)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____4473)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____4497 -> tm
                      else
                        (let uu____4507 =
                           (FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Syntax_Const.forall_lid)
                             ||
                             (FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid) in
                         if uu____4507
                         then
                           match args with
                           | (t,_)::[]
                             |(_,Some (FStar_Syntax_Syntax.Implicit _))::
                             (t,_)::[] ->
                               let uu____4548 =
                                 let uu____4549 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____4549.FStar_Syntax_Syntax.n in
                               (match uu____4548 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____4552::[],body,uu____4554) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | Some (false ) ->
                                         w FStar_Syntax_Util.t_false
                                     | uu____4580 -> tm)
                                | uu____4582 -> tm)
                           | uu____4583 -> tm
                         else reduce_equality cfg tm))))
         | uu____4590 -> tm)
let is_norm_request hd1 args =
  let uu____4605 =
    let uu____4609 =
      let uu____4610 = FStar_Syntax_Util.un_uinst hd1 in
      uu____4610.FStar_Syntax_Syntax.n in
    (uu____4609, args) in
  match uu____4605 with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4615::uu____4616::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize_term
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4619::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize
  | uu____4621 -> false
let get_norm_request args =
  match args with
  | _::(tm,_)::[]|(tm,_)::[] -> tm
  | uu____4654 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___137_4661  ->
    match uu___137_4661 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.tk = uu____4663;
           FStar_Syntax_Syntax.pos = uu____4664;
           FStar_Syntax_Syntax.vars = uu____4665;_},uu____4666,uu____4667))::uu____4668
        -> true
    | uu____4674 -> false
let is_fstar_tactics_quote: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____4679 =
      let uu____4680 = FStar_Syntax_Util.un_uinst t in
      uu____4680.FStar_Syntax_Syntax.n in
    match uu____4679 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Syntax_Const.fstar_tactics_quote_lid
    | uu____4684 -> false
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
            (fun uu____4800  ->
               let uu____4801 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____4802 = FStar_Syntax_Print.term_to_string t1 in
               let uu____4803 =
                 let uu____4804 =
                   let uu____4806 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left Prims.fst uu____4806 in
                 stack_to_string uu____4804 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____4801
                 uu____4802 uu____4803);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____4818 ->
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
           | FStar_Syntax_Syntax.Tm_app
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.tk = uu____4850;
                  FStar_Syntax_Syntax.pos = uu____4851;
                  FStar_Syntax_Syntax.vars = uu____4852;_},uu____4853)
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Syntax_Const.fstar_tactics_embed_lid
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               is_fstar_tactics_quote hd1 ->
               let args1 = closures_as_args_delayed cfg env args in
               let t2 =
                 let uu___163_4893 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd1, args1));
                   FStar_Syntax_Syntax.tk =
                     (uu___163_4893.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___163_4893.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___163_4893.FStar_Syntax_Syntax.vars)
                 } in
               let t3 = reduce_primops cfg t2 in rebuild cfg env stack1 t3
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____4922 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____4922) && (is_norm_request hd1 args))
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
                 let uu___164_4935 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___164_4935.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___164_4935.primitive_steps)
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
                  FStar_Syntax_Syntax.tk = uu____4940;
                  FStar_Syntax_Syntax.pos = uu____4941;
                  FStar_Syntax_Syntax.vars = uu____4942;_},a1::a2::rest)
               ->
               let uu____4976 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____4976 with
                | (hd1,uu____4987) ->
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
                    (FStar_Const.Const_reflect uu____5042);
                  FStar_Syntax_Syntax.tk = uu____5043;
                  FStar_Syntax_Syntax.pos = uu____5044;
                  FStar_Syntax_Syntax.vars = uu____5045;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____5068 = FStar_List.tl stack1 in
               norm cfg env uu____5068 (Prims.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.tk = uu____5071;
                  FStar_Syntax_Syntax.pos = uu____5072;
                  FStar_Syntax_Syntax.vars = uu____5073;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____5096 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____5096 with
                | (reify_head,uu____5107) ->
                    let a1 =
                      let uu____5123 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (Prims.fst a) in
                      FStar_Syntax_Subst.compress uu____5123 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____5126);
                            FStar_Syntax_Syntax.tk = uu____5127;
                            FStar_Syntax_Syntax.pos = uu____5128;
                            FStar_Syntax_Syntax.vars = uu____5129;_},a2::[])
                         -> norm cfg env stack1 (Prims.fst a2)
                     | uu____5154 ->
                         let stack2 =
                           (App
                              (reify_head, None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____5162 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____5162
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____5169 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____5169
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____5172 =
                      let uu____5176 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____5176, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____5172 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___138_5185  ->
                         match uu___138_5185 with
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
                    let uu____5189 = FStar_Syntax_Syntax.range_of_fv f in
                    FStar_TypeChecker_Env.set_range cfg.tcenv uu____5189 in
                  let uu____5190 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  match uu____5190 with
                  | None  ->
                      (log cfg
                         (fun uu____5201  ->
                            FStar_Util.print "Tm_fvar case 2\n" []);
                       rebuild cfg env stack1 t1)
                  | Some (us,t2) ->
                      (log cfg
                         (fun uu____5207  ->
                            let uu____5208 =
                              FStar_Syntax_Print.term_to_string t0 in
                            let uu____5209 =
                              FStar_Syntax_Print.term_to_string t2 in
                            FStar_Util.print2 ">>> Unfolded %s to %s\n"
                              uu____5208 uu____5209);
                       (let n1 = FStar_List.length us in
                        if n1 > (Prims.parse_int "0")
                        then
                          match stack1 with
                          | (UnivArgs (us',uu____5216))::stack2 ->
                              let env1 =
                                FStar_All.pipe_right us'
                                  (FStar_List.fold_left
                                     (fun env1  -> fun u  -> (Univ u) :: env1)
                                     env) in
                              norm cfg env1 stack2 t2
                          | uu____5229 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack1 t2
                          | uu____5230 ->
                              let uu____5231 =
                                let uu____5232 =
                                  FStar_Syntax_Print.lid_to_string
                                    (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                FStar_Util.format1
                                  "Impossible: missing universe instantiation on %s"
                                  uu____5232 in
                              failwith uu____5231
                        else norm cfg env stack1 t2)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____5239 = lookup_bvar env x in
               (match uu____5239 with
                | Univ uu____5240 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____5255 = FStar_ST.read r in
                      (match uu____5255 with
                       | Some (env2,t') ->
                           (log cfg
                              (fun uu____5274  ->
                                 let uu____5275 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____5276 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____5275
                                   uu____5276);
                            (let uu____5277 =
                               let uu____5278 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____5278.FStar_Syntax_Syntax.n in
                             match uu____5277 with
                             | FStar_Syntax_Syntax.Tm_abs uu____5281 ->
                                 norm cfg env2 stack1 t'
                             | uu____5296 -> rebuild cfg env2 stack1 t'))
                       | None  -> norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____5329)::uu____5330 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____5335)::uu____5336 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____5342,uu____5343))::stack_rest ->
                    (match c with
                     | Univ uu____5346 -> norm cfg (c :: env) stack_rest t1
                     | uu____5347 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____5350::[] ->
                              (match lopt with
                               | None  when FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____5363  ->
                                         let uu____5364 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____5364);
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
                                           (fun uu___139_5378  ->
                                              match uu___139_5378 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____5379 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____5381  ->
                                         let uu____5382 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____5382);
                                    norm cfg (c :: env) stack_rest body)
                               | Some (FStar_Util.Inl lc) when
                                   FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                                   ->
                                   (log cfg
                                      (fun uu____5393  ->
                                         let uu____5394 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____5394);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____5395 when
                                   FStar_All.pipe_right cfg.steps
                                     (FStar_List.contains Reify)
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____5402 ->
                                   let cfg1 =
                                     let uu___165_5410 = cfg in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___165_5410.tcenv);
                                       delta_level =
                                         (uu___165_5410.delta_level);
                                       primitive_steps =
                                         (uu___165_5410.primitive_steps)
                                     } in
                                   let uu____5411 =
                                     closure_as_term cfg1 env t1 in
                                   rebuild cfg1 env stack1 uu____5411)
                          | uu____5412::tl1 ->
                              (log cfg
                                 (fun uu____5422  ->
                                    let uu____5423 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____5423);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___166_5447 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___166_5447.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____5460  ->
                          let uu____5461 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____5461);
                     norm cfg env stack2 t1)
                | (Debug _)::_
                  |(Meta _)::_|(Let _)::_|(App _)::_|(Abs _)::_|[] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____5472 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____5472
                    else
                      (let uu____5474 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____5474 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____5503 =
                                   let uu____5509 =
                                     let uu____5510 =
                                       let uu____5511 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____5511 in
                                     FStar_All.pipe_right uu____5510
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____5509
                                     (fun _0_30  -> FStar_Util.Inl _0_30) in
                                 FStar_All.pipe_right uu____5503
                                   (fun _0_31  -> Some _0_31)
                             | uu____5536 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____5550  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____5555  ->
                                 let uu____5556 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____5556);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___167_5566 = cfg in
                               let uu____5567 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___167_5566.steps);
                                 tcenv = (uu___167_5566.tcenv);
                                 delta_level = (uu___167_5566.delta_level);
                                 primitive_steps = uu____5567
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
                      (fun uu____5599  ->
                         fun stack2  ->
                           match uu____5599 with
                           | (a,aq) ->
                               let uu____5607 =
                                 let uu____5608 =
                                   let uu____5612 =
                                     let uu____5613 =
                                       let uu____5623 =
                                         FStar_Util.mk_ref None in
                                       (env, a, uu____5623, false) in
                                     Clos uu____5613 in
                                   (uu____5612, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____5608 in
                               uu____5607 :: stack2) args) in
               (log cfg
                  (fun uu____5645  ->
                     let uu____5646 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____5646);
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
                             ((let uu___168_5667 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___168_5667.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___168_5667.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____5668 ->
                      let uu____5671 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____5671)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____5674 = FStar_Syntax_Subst.open_term [(x, None)] f in
                  match uu____5674 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____5690 =
                          let uu____5691 =
                            let uu____5696 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___169_5697 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___169_5697.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___169_5697.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____5696) in
                          FStar_Syntax_Syntax.Tm_refine uu____5691 in
                        mk uu____5690 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____5710 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____5710
               else
                 (let uu____5712 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____5712 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____5718 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  -> fun uu____5724  -> Dummy :: env1)
                               env) in
                        norm_comp cfg uu____5718 c1 in
                      let t2 =
                        let uu____5731 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____5731 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
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
                | uu____5788 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____5791  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____5804 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____5804
                        | FStar_Util.Inr c ->
                            let uu____5812 = norm_comp cfg env c in
                            FStar_Util.Inr uu____5812 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____5817 =
                        mk
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (t12, (tc1, tacopt1), l))
                          t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____5817)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____5868,{
                              FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                uu____5869;
                              FStar_Syntax_Syntax.lbunivs = uu____5870;
                              FStar_Syntax_Syntax.lbtyp = uu____5871;
                              FStar_Syntax_Syntax.lbeff = uu____5872;
                              FStar_Syntax_Syntax.lbdef = uu____5873;_}::uu____5874),uu____5875)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____5901 =
                 (let uu____5902 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____5902) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____5903 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____5903))) in
               if uu____5901
               then
                 let env1 =
                   let uu____5906 =
                     let uu____5907 =
                       let uu____5917 = FStar_Util.mk_ref None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____5917,
                         false) in
                     Clos uu____5907 in
                   uu____5906 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____5941 =
                    let uu____5944 =
                      let uu____5945 =
                        let uu____5946 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____5946
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____5945] in
                    FStar_Syntax_Subst.open_term uu____5944 body in
                  match uu____5941 with
                  | (bs,body1) ->
                      let lb1 =
                        let uu___170_5952 = lb in
                        let uu____5953 =
                          let uu____5956 =
                            let uu____5957 = FStar_List.hd bs in
                            FStar_All.pipe_right uu____5957 Prims.fst in
                          FStar_All.pipe_right uu____5956
                            (fun _0_32  -> FStar_Util.Inl _0_32) in
                        let uu____5966 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____5969 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = uu____5953;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___170_5952.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____5966;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___170_5952.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5969
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____5979  -> Dummy :: env1)
                             env) in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____5995 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____5995
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____6008 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____6030  ->
                        match uu____6030 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____6069 =
                                let uu___171_6070 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___171_6070.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___171_6070.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____6069 in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos in
                            let memo = FStar_Util.mk_ref None in
                            let rec_env1 = (Clos (env, fix_f_i, memo, true))
                              :: rec_env in
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1")))) (Prims.snd lbs)
                   (env, [], (Prims.parse_int "0")) in
               (match uu____6008 with
                | (rec_env,memos,uu____6130) ->
                    let uu____6145 =
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
                             let uu____6187 =
                               let uu____6188 =
                                 let uu____6198 = FStar_Util.mk_ref None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____6198, false) in
                               Clos uu____6188 in
                             uu____6187 :: env1) (Prims.snd lbs) env in
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
                             FStar_Syntax_Syntax.tk = uu____6236;
                             FStar_Syntax_Syntax.pos = uu____6237;
                             FStar_Syntax_Syntax.vars = uu____6238;_},uu____6239,uu____6240))::uu____6241
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____6247 -> false in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____6254 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____6254
                        then
                          let uu___172_6255 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___172_6255.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps = (uu___172_6255.primitive_steps)
                          }
                        else
                          (let uu___173_6257 = cfg in
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___173_6257.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta];
                             primitive_steps =
                               (uu___173_6257.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____6259 =
                         let uu____6260 = FStar_Syntax_Subst.compress head1 in
                         uu____6260.FStar_Syntax_Syntax.n in
                       match uu____6259 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____6274 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____6274 with
                            | (uu____6275,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____6279 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____6286 =
                                         let uu____6287 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____6287.FStar_Syntax_Syntax.n in
                                       match uu____6286 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____6292,uu____6293))
                                           ->
                                           let uu____6302 =
                                             let uu____6303 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____6303.FStar_Syntax_Syntax.n in
                                           (match uu____6302 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____6308,msrc,uu____6310))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____6319 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                Some uu____6319
                                            | uu____6320 -> None)
                                       | uu____6321 -> None in
                                     let uu____6322 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____6322 with
                                      | Some e ->
                                          let lb1 =
                                            let uu___174_6326 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___174_6326.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___174_6326.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___174_6326.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Syntax_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____6327 =
                                            FStar_List.tl stack1 in
                                          let uu____6328 =
                                            let uu____6329 =
                                              let uu____6332 =
                                                let uu____6333 =
                                                  let uu____6341 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____6341) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____6333 in
                                              FStar_Syntax_Syntax.mk
                                                uu____6332 in
                                            uu____6329 None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____6327 uu____6328
                                      | None  ->
                                          let uu____6358 =
                                            let uu____6359 = is_return body in
                                            match uu____6359 with
                                            | Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____6362;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____6363;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____6364;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____6369 -> false in
                                          if uu____6358
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
                                               let uu____6389 =
                                                 let uu____6392 =
                                                   let uu____6393 =
                                                     let uu____6408 =
                                                       let uu____6410 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____6410] in
                                                     (uu____6408, body1,
                                                       (Some
                                                          (FStar_Util.Inr
                                                             (m1, [])))) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____6393 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____6392 in
                                               uu____6389 None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____6443 =
                                                 let uu____6444 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____6444.FStar_Syntax_Syntax.n in
                                               match uu____6443 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____6450::uu____6451::[])
                                                   ->
                                                   let uu____6457 =
                                                     let uu____6460 =
                                                       let uu____6461 =
                                                         let uu____6466 =
                                                           let uu____6468 =
                                                             let uu____6469 =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____6469 in
                                                           let uu____6470 =
                                                             let uu____6472 =
                                                               let uu____6473
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____6473 in
                                                             [uu____6472] in
                                                           uu____6468 ::
                                                             uu____6470 in
                                                         (bind1, uu____6466) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____6461 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____6460 in
                                                   uu____6457 None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____6485 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____6491 =
                                                 let uu____6494 =
                                                   let uu____6495 =
                                                     let uu____6505 =
                                                       let uu____6507 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____6508 =
                                                         let uu____6510 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____6511 =
                                                           let uu____6513 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____6514 =
                                                             let uu____6516 =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____6517 =
                                                               let uu____6519
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____6520
                                                                 =
                                                                 let uu____6522
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____6522] in
                                                               uu____6519 ::
                                                                 uu____6520 in
                                                             uu____6516 ::
                                                               uu____6517 in
                                                           uu____6513 ::
                                                             uu____6514 in
                                                         uu____6510 ::
                                                           uu____6511 in
                                                       uu____6507 ::
                                                         uu____6508 in
                                                     (bind_inst, uu____6505) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____6495 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____6494 in
                                               uu____6491 None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____6534 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____6534 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____6552 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____6552 with
                            | (uu____6553,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____6576 =
                                        let uu____6577 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____6577.FStar_Syntax_Syntax.n in
                                      match uu____6576 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____6583) -> t4
                                      | uu____6588 -> head2 in
                                    let uu____6589 =
                                      let uu____6590 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____6590.FStar_Syntax_Syntax.n in
                                    match uu____6589 with
                                    | FStar_Syntax_Syntax.Tm_fvar x -> Some x
                                    | uu____6595 -> None in
                                  let uu____6596 = maybe_extract_fv head2 in
                                  match uu____6596 with
                                  | Some x when
                                      let uu____6602 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____6602
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____6606 =
                                          maybe_extract_fv head3 in
                                        match uu____6606 with
                                        | Some uu____6609 -> Some true
                                        | uu____6610 -> Some false in
                                      (head3, action_unfolded)
                                  | uu____6613 -> (head2, None) in
                                ((let is_arg_impure uu____6624 =
                                    match uu____6624 with
                                    | (e,q) ->
                                        let uu____6629 =
                                          let uu____6630 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____6630.FStar_Syntax_Syntax.n in
                                        (match uu____6629 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____6645 -> false) in
                                  let uu____6646 =
                                    let uu____6647 =
                                      let uu____6651 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____6651 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____6647 in
                                  if uu____6646
                                  then
                                    let uu____6654 =
                                      let uu____6655 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____6655 in
                                    failwith uu____6654
                                  else ());
                                 (let uu____6657 =
                                    maybe_unfold_action head_app in
                                  match uu____6657 with
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
                                      let uu____6692 = FStar_List.tl stack1 in
                                      norm cfg env uu____6692 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted = reify_lift cfg.tcenv e msrc mtgt t' in
                           let uu____6706 = FStar_List.tl stack1 in
                           norm cfg env uu____6706 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____6789  ->
                                     match uu____6789 with
                                     | (pat,wopt,tm) ->
                                         let uu____6827 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____6827))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____6853 = FStar_List.tl stack1 in
                           norm cfg env uu____6853 tm
                       | uu____6854 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.tk = uu____6863;
                             FStar_Syntax_Syntax.pos = uu____6864;
                             FStar_Syntax_Syntax.vars = uu____6865;_},uu____6866,uu____6867))::uu____6868
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____6874 -> false in
                    if should_reify
                    then
                      let uu____6875 = FStar_List.tl stack1 in
                      let uu____6876 = reify_lift cfg.tcenv head1 m1 m' t2 in
                      norm cfg env uu____6875 uu____6876
                    else
                      (let uu____6878 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____6878
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___175_6884 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___175_6884.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___175_6884.primitive_steps)
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
                | uu____6890 ->
                    (match stack1 with
                     | uu____6891::uu____6892 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____6896)
                              -> norm cfg env ((Meta (m, r)) :: stack1) head1
                          | FStar_Syntax_Syntax.Meta_pattern args ->
                              let args1 = norm_pattern_args cfg env args in
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_pattern args1),
                                      (t1.FStar_Syntax_Syntax.pos))) ::
                                stack1) head1
                          | uu____6911 -> norm cfg env stack1 head1)
                     | [] ->
                         let head2 = norm cfg env [] head1 in
                         let m1 =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               let uu____6921 =
                                 norm_pattern_args cfg env args in
                               FStar_Syntax_Syntax.Meta_pattern uu____6921
                           | uu____6928 -> m in
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
              let uu____6942 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____6942 with
              | (uu____6943,return_repr) ->
                  let return_inst =
                    let uu____6950 =
                      let uu____6951 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____6951.FStar_Syntax_Syntax.n in
                    match uu____6950 with
                    | FStar_Syntax_Syntax.Tm_uinst (return_tm,uu____6957::[])
                        ->
                        let uu____6963 =
                          let uu____6966 =
                            let uu____6967 =
                              let uu____6972 =
                                let uu____6974 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____6974] in
                              (return_tm, uu____6972) in
                            FStar_Syntax_Syntax.Tm_uinst uu____6967 in
                          FStar_Syntax_Syntax.mk uu____6966 in
                        uu____6963 None e.FStar_Syntax_Syntax.pos
                    | uu____6986 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____6989 =
                    let uu____6992 =
                      let uu____6993 =
                        let uu____7003 =
                          let uu____7005 = FStar_Syntax_Syntax.as_arg t in
                          let uu____7006 =
                            let uu____7008 = FStar_Syntax_Syntax.as_arg e in
                            [uu____7008] in
                          uu____7005 :: uu____7006 in
                        (return_inst, uu____7003) in
                      FStar_Syntax_Syntax.Tm_app uu____6993 in
                    FStar_Syntax_Syntax.mk uu____6992 in
                  uu____6989 None e.FStar_Syntax_Syntax.pos
            else
              (let uu____7021 = FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____7021 with
               | None  ->
                   let uu____7023 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____7023
               | Some
                   { FStar_TypeChecker_Env.msource = uu____7024;
                     FStar_TypeChecker_Env.mtarget = uu____7025;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____7026;
                         FStar_TypeChecker_Env.mlift_term = None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | Some
                   { FStar_TypeChecker_Env.msource = uu____7037;
                     FStar_TypeChecker_Env.mtarget = uu____7038;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____7039;
                         FStar_TypeChecker_Env.mlift_term = Some lift;_};_}
                   ->
                   let uu____7057 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____7057)
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
                (fun uu____7087  ->
                   match uu____7087 with
                   | (a,imp) ->
                       let uu____7094 = norm cfg env [] a in
                       (uu____7094, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___176_7109 = comp1 in
            let uu____7112 =
              let uu____7113 =
                let uu____7119 = norm cfg env [] t in
                let uu____7120 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____7119, uu____7120) in
              FStar_Syntax_Syntax.Total uu____7113 in
            {
              FStar_Syntax_Syntax.n = uu____7112;
              FStar_Syntax_Syntax.tk = (uu___176_7109.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___176_7109.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___176_7109.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___177_7135 = comp1 in
            let uu____7138 =
              let uu____7139 =
                let uu____7145 = norm cfg env [] t in
                let uu____7146 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____7145, uu____7146) in
              FStar_Syntax_Syntax.GTotal uu____7139 in
            {
              FStar_Syntax_Syntax.n = uu____7138;
              FStar_Syntax_Syntax.tk = (uu___177_7135.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___177_7135.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___177_7135.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____7177  ->
                      match uu____7177 with
                      | (a,i) ->
                          let uu____7184 = norm cfg env [] a in
                          (uu____7184, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___140_7189  ->
                      match uu___140_7189 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____7193 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____7193
                      | f -> f)) in
            let uu___178_7197 = comp1 in
            let uu____7200 =
              let uu____7201 =
                let uu___179_7202 = ct in
                let uu____7203 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____7204 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____7207 = norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____7203;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___179_7202.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____7204;
                  FStar_Syntax_Syntax.effect_args = uu____7207;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____7201 in
            {
              FStar_Syntax_Syntax.n = uu____7200;
              FStar_Syntax_Syntax.tk = (uu___178_7197.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___178_7197.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___178_7197.FStar_Syntax_Syntax.vars)
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
            (let uu___180_7224 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___180_7224.tcenv);
               delta_level = (uu___180_7224.delta_level);
               primitive_steps = (uu___180_7224.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____7229 = norm1 t in
          FStar_Syntax_Util.non_informative uu____7229 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____7232 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___181_7246 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.tk = (uu___181_7246.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___181_7246.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___181_7246.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____7256 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____7256
            then
              let ct1 =
                match downgrade_ghost_effect_name
                        ct.FStar_Syntax_Syntax.effect_name
                with
                | Some pure_eff ->
                    let uu___182_7261 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___182_7261.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___182_7261.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___182_7261.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___182_7261.FStar_Syntax_Syntax.flags)
                    }
                | None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___183_7263 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___183_7263.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Syntax_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___183_7263.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___183_7263.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___183_7263.FStar_Syntax_Syntax.flags)
                    } in
              let uu___184_7264 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.tk =
                  (uu___184_7264.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___184_7264.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___184_7264.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____7270 -> c
and norm_binder:
  cfg ->
    env ->
      FStar_Syntax_Syntax.binder ->
        (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  =
  fun cfg  ->
    fun env  ->
      fun uu____7273  ->
        match uu____7273 with
        | (x,imp) ->
            let uu____7276 =
              let uu___185_7277 = x in
              let uu____7278 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___185_7277.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___185_7277.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____7278
              } in
            (uu____7276, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____7284 =
          FStar_List.fold_left
            (fun uu____7291  ->
               fun b  ->
                 match uu____7291 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____7284 with | (nbs,uu____7308) -> FStar_List.rev nbs
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
            let uu____7325 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
            if uu____7325
            then
              let t = norm cfg env [] lc.FStar_Syntax_Syntax.res_typ in
              let uu____7330 = FStar_Syntax_Util.is_total_lcomp lc in
              (if uu____7330
               then
                 let uu____7334 =
                   let uu____7337 =
                     let uu____7338 =
                       let uu____7341 = FStar_Syntax_Syntax.mk_Total t in
                       FStar_Syntax_Util.comp_set_flags uu____7341 flags in
                     FStar_Syntax_Util.lcomp_of_comp uu____7338 in
                   FStar_Util.Inl uu____7337 in
                 Some uu____7334
               else
                 (let uu____7345 =
                    let uu____7348 =
                      let uu____7349 =
                        let uu____7352 = FStar_Syntax_Syntax.mk_GTotal t in
                        FStar_Syntax_Util.comp_set_flags uu____7352 flags in
                      FStar_Syntax_Util.lcomp_of_comp uu____7349 in
                    FStar_Util.Inl uu____7348 in
                  Some uu____7345))
            else
              Some
                (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags))
        | uu____7365 -> lopt
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
              ((let uu____7377 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____7377
                then
                  let uu____7378 = FStar_Syntax_Print.term_to_string tm in
                  let uu____7379 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2 "Normalized %s to %s\n" uu____7378
                    uu____7379
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___186_7390 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___186_7390.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____7410  ->
                    let uu____7411 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____7411);
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
              let uu____7448 =
                let uu___187_7449 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___187_7449.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___187_7449.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___187_7449.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____7448
          | (Arg (Univ _,_,_))::_|(Arg (Dummy ,_,_))::_ ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____7471),aq,r))::stack2 ->
              (log cfg
                 (fun uu____7487  ->
                    let uu____7488 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____7488);
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
                 (let uu____7499 = FStar_ST.read m in
                  match uu____7499 with
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
                  | Some (uu____7525,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq) None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.extend_app head1 (t, aq) None r in
              let uu____7547 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____7547
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____7554  ->
                    let uu____7555 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____7555);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____7560 =
                  log cfg
                    (fun uu____7562  ->
                       let uu____7563 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____7564 =
                         let uu____7565 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____7572  ->
                                   match uu____7572 with
                                   | (p,uu____7578,uu____7579) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____7565
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____7563 uu____7564);
                  (let whnf = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___141_7589  ->
                               match uu___141_7589 with
                               | FStar_TypeChecker_Env.Inlining 
                                 |FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____7590 -> false)) in
                     let steps' =
                       let uu____7593 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____7593
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___188_7596 = cfg in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___188_7596.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___188_7596.primitive_steps)
                     } in
                   let norm_or_whnf env2 t1 =
                     if whnf
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____7630 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_disj [] ->
                         failwith "Impossible"
                     | FStar_Syntax_Syntax.Pat_disj (hd1::tl1) ->
                         let uu____7650 = norm_pat env2 hd1 in
                         (match uu____7650 with
                          | (hd2,env') ->
                              let tl2 =
                                FStar_All.pipe_right tl1
                                  (FStar_List.map
                                     (fun p1  ->
                                        let uu____7686 = norm_pat env2 p1 in
                                        Prims.fst uu____7686)) in
                              ((let uu___189_7698 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_disj (hd2 ::
                                       tl2));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___189_7698.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___189_7698.FStar_Syntax_Syntax.p)
                                }), env'))
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____7715 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____7749  ->
                                   fun uu____7750  ->
                                     match (uu____7749, uu____7750) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____7815 = norm_pat env3 p1 in
                                         (match uu____7815 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____7715 with
                          | (pats1,env3) ->
                              ((let uu___190_7881 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___190_7881.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___190_7881.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___191_7895 = x in
                           let uu____7896 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___191_7895.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___191_7895.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____7896
                           } in
                         ((let uu___192_7902 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___192_7902.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___192_7902.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___193_7907 = x in
                           let uu____7908 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___193_7907.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___193_7907.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____7908
                           } in
                         ((let uu___194_7914 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___194_7914.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___194_7914.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___195_7924 = x in
                           let uu____7925 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___195_7924.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___195_7924.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____7925
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___196_7932 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.ty =
                               (uu___196_7932.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___196_7932.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf -> branches
                     | uu____7936 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____7939 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____7939 with
                                 | (p,wopt,e) ->
                                     let uu____7957 = norm_pat env1 p in
                                     (match uu____7957 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | None  -> None
                                            | Some w ->
                                                let uu____7981 =
                                                  norm_or_whnf env2 w in
                                                Some uu____7981 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____7986 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____7986) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____7996) -> is_cons h
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
                  | uu____8007 -> false in
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
                  let uu____8106 = FStar_Syntax_Util.head_and_args scrutinee2 in
                  match uu____8106 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_disj ps ->
                           let mopt =
                             FStar_Util.find_map ps
                               (fun p1  ->
                                  let m = matches_pat scrutinee2 p1 in
                                  match m with
                                  | FStar_Util.Inl uu____8163 -> Some m
                                  | FStar_Util.Inr (true ) -> Some m
                                  | FStar_Util.Inr (false ) -> None) in
                           (match mopt with
                            | None  -> FStar_Util.Inr false
                            | Some m -> m)
                       | FStar_Syntax_Syntax.Pat_var _
                         |FStar_Syntax_Syntax.Pat_wild _ ->
                           FStar_Util.Inl [scrutinee2]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____8194 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____8206 ->
                                let uu____8207 =
                                  let uu____8208 = is_cons head1 in
                                  Prims.op_Negation uu____8208 in
                                FStar_Util.Inr uu____8207)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____8222 =
                             let uu____8223 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____8223.FStar_Syntax_Syntax.n in
                           (match uu____8222 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____8230 ->
                                let uu____8231 =
                                  let uu____8232 = is_cons head1 in
                                  Prims.op_Negation uu____8232 in
                                FStar_Util.Inr uu____8231))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____8266)::rest_a,(p1,uu____8269)::rest_p) ->
                      let uu____8297 = matches_pat t1 p1 in
                      (match uu____8297 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____8311 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____8382 = matches_pat scrutinee1 p1 in
                      (match uu____8382 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____8392  ->
                                 let uu____8393 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____8394 =
                                   let uu____8395 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____8395
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____8393 uu____8394);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____8404 =
                                        let uu____8405 =
                                          let uu____8415 =
                                            FStar_Util.mk_ref (Some ([], t1)) in
                                          ([], t1, uu____8415, false) in
                                        Clos uu____8405 in
                                      uu____8404 :: env2) env1 s in
                             let uu____8438 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____8438))) in
                let uu____8439 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____8439
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___142_8453  ->
                match uu___142_8453 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | uu____8456 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____8460 -> d in
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
            let uu___197_8480 = config s e in
            {
              steps = (uu___197_8480.steps);
              tcenv = (uu___197_8480.tcenv);
              delta_level = (uu___197_8480.delta_level);
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
      fun t  -> let uu____8499 = config s e in norm_comp uu____8499 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  -> let uu____8506 = config [] env in norm_universe uu____8506 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun c  ->
      let uu____8513 = config [] env in ghost_to_pure_aux uu____8513 [] c
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
        let uu____8525 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____8525 in
      let uu____8526 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____8526
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | Some pure_eff ->
            let uu___198_8528 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___198_8528.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___198_8528.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____8529  ->
                    let uu____8530 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____8530))
            }
        | None  -> lc
      else lc
let term_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun env  ->
    fun t  ->
      let uu____8538 = normalize [AllowUnboundUniverses] env t in
      FStar_Syntax_Print.term_to_string uu____8538
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let uu____8545 =
        let uu____8546 = config [AllowUnboundUniverses] env in
        norm_comp uu____8546 [] c in
      FStar_Syntax_Print.comp_to_string uu____8545
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
                   let uu____8583 =
                     let uu____8584 =
                       let uu____8589 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____8589) in
                     FStar_Syntax_Syntax.Tm_refine uu____8584 in
                   mk uu____8583 t01.FStar_Syntax_Syntax.pos
               | uu____8594 -> t2)
          | uu____8595 -> t2 in
        aux t
let unfold_whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      normalize [WHNF; UnfoldUntil FStar_Syntax_Syntax.Delta_constant; Beta]
        env t
let eta_expand_with_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      fun t_e  ->
        let uu____8611 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____8611 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____8627 ->
                 let uu____8631 = FStar_Syntax_Util.abs_formals e in
                 (match uu____8631 with
                  | (actuals,uu____8642,uu____8643) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____8665 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____8665 with
                         | (binders,args) ->
                             let uu____8675 =
                               (FStar_Syntax_Syntax.mk_Tm_app e args) None
                                 e.FStar_Syntax_Syntax.pos in
                             let uu____8680 =
                               let uu____8687 =
                                 FStar_All.pipe_right
                                   (FStar_Syntax_Util.lcomp_of_comp c)
                                   (fun _0_33  -> FStar_Util.Inl _0_33) in
                               FStar_All.pipe_right uu____8687
                                 (fun _0_34  -> Some _0_34) in
                             FStar_Syntax_Util.abs binders uu____8675
                               uu____8680)))
let eta_expand:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____8723 =
        let uu____8727 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
        (uu____8727, (t.FStar_Syntax_Syntax.n)) in
      match uu____8723 with
      | (Some sort,uu____8734) ->
          let uu____8736 = mk sort t.FStar_Syntax_Syntax.pos in
          eta_expand_with_type env t uu____8736
      | (uu____8737,FStar_Syntax_Syntax.Tm_name x) ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____8741 ->
          let uu____8745 = FStar_Syntax_Util.head_and_args t in
          (match uu____8745 with
           | (head1,args) ->
               let uu____8771 =
                 let uu____8772 = FStar_Syntax_Subst.compress head1 in
                 uu____8772.FStar_Syntax_Syntax.n in
               (match uu____8771 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____8775,thead) ->
                    let uu____8789 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____8789 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____8820 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___199_8824 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___199_8824.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___199_8824.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___199_8824.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___199_8824.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___199_8824.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___199_8824.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ = None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___199_8824.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___199_8824.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___199_8824.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___199_8824.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___199_8824.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___199_8824.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___199_8824.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___199_8824.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___199_8824.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___199_8824.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___199_8824.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___199_8824.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___199_8824.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___199_8824.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___199_8824.FStar_TypeChecker_Env.qname_and_index)
                                 }) t in
                            match uu____8820 with
                            | (uu____8825,ty,uu____8827) ->
                                eta_expand_with_type env t ty))
                | uu____8828 ->
                    let uu____8829 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___200_8833 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___200_8833.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___200_8833.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___200_8833.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___200_8833.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___200_8833.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___200_8833.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ = None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___200_8833.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___200_8833.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___200_8833.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___200_8833.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___200_8833.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___200_8833.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___200_8833.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___200_8833.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___200_8833.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___200_8833.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___200_8833.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___200_8833.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___200_8833.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___200_8833.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___200_8833.FStar_TypeChecker_Env.qname_and_index)
                         }) t in
                    (match uu____8829 with
                     | (uu____8834,ty,uu____8836) ->
                         eta_expand_with_type env t ty)))