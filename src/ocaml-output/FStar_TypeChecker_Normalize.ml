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
  fun uu___133_219  ->
    match uu___133_219 with
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
  fun uu___134_658  ->
    match uu___134_658 with
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
let is_empty uu___135_739 =
  match uu___135_739 with | [] -> true | uu____741 -> false
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
                    let uu___148_1564 = lb in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___148_1564.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___148_1564.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = typ;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___148_1564.FStar_Syntax_Syntax.lbeff);
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
                    let uu___149_1607 = lb in
                    let uu____1608 =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let uu____1611 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___149_1607.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___149_1607.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = uu____1608;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___149_1607.FStar_Syntax_Syntax.lbeff);
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
                                   ((let uu___150_1791 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_disj (hd2
                                            :: tl2));
                                       FStar_Syntax_Syntax.ty =
                                         (uu___150_1791.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___150_1791.FStar_Syntax_Syntax.p)
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
                                   ((let uu___151_1974 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.ty =
                                         (uu___151_1974.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___151_1974.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___152_1988 = x in
                                let uu____1989 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___152_1988.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___152_1988.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1989
                                } in
                              ((let uu___153_1995 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___153_1995.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___153_1995.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___154_2000 = x in
                                let uu____2001 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___154_2000.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___154_2000.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____2001
                                } in
                              ((let uu___155_2007 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___155_2007.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___155_2007.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___156_2017 = x in
                                let uu____2018 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___156_2017.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___156_2017.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____2018
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___157_2025 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___157_2025.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___157_2025.FStar_Syntax_Syntax.p)
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
                          let uu___158_2249 = b in
                          let uu____2250 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___158_2249.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___158_2249.FStar_Syntax_Syntax.index);
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
                        (fun uu___136_2337  ->
                           match uu___136_2337 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____2341 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____2341
                           | f -> f)) in
                 let uu____2345 =
                   let uu___159_2346 = c1 in
                   let uu____2347 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____2347;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___159_2346.FStar_Syntax_Syntax.effect_name);
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
         (fun uu___137_2351  ->
            match uu___137_2351 with
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
  let arg_as_char uu____2589 =
    match uu____2589 with
    | (a,uu____2594) ->
        let uu____2596 =
          let uu____2597 = FStar_Syntax_Subst.compress a in
          uu____2597.FStar_Syntax_Syntax.n in
        (match uu____2596 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
             Some c
         | uu____2602 -> None) in
  let arg_as_string uu____2609 =
    match uu____2609 with
    | (a,uu____2614) ->
        let uu____2616 =
          let uu____2617 = FStar_Syntax_Subst.compress a in
          uu____2617.FStar_Syntax_Syntax.n in
        (match uu____2616 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (bytes,uu____2622)) -> Some (FStar_Util.string_of_bytes bytes)
         | uu____2625 -> None) in
  let arg_as_list f uu____2646 =
    match uu____2646 with
    | (a,uu____2655) ->
        let rec sequence l =
          match l with
          | [] -> Some []
          | (None )::uu____2674 -> None
          | (Some x)::xs ->
              let uu____2684 = sequence xs in
              (match uu____2684 with
               | None  -> None
               | Some xs' -> Some (x :: xs')) in
        let uu____2695 = FStar_Syntax_Util.list_elements a in
        (match uu____2695 with
         | None  -> None
         | Some elts ->
             let uu____2705 =
               FStar_List.map
                 (fun x  ->
                    let uu____2710 = FStar_Syntax_Syntax.as_arg x in
                    f uu____2710) elts in
             sequence uu____2705) in
  let lift_unary f aopts =
    match aopts with
    | (Some a)::[] -> let uu____2740 = f a in Some uu____2740
    | uu____2741 -> None in
  let lift_binary f aopts =
    match aopts with
    | (Some a0)::(Some a1)::[] -> let uu____2780 = f a0 a1 in Some uu____2780
    | uu____2781 -> None in
  let unary_op as_a f r args =
    let uu____2825 = FStar_List.map as_a args in lift_unary (f r) uu____2825 in
  let binary_op as_a f r args =
    let uu____2875 = FStar_List.map as_a args in lift_binary (f r) uu____2875 in
  let as_primitive_step uu____2892 =
    match uu____2892 with
    | (l,arity,f) ->
        { name = l; arity; strong_reduction_ok = true; interpretation = f } in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  -> fun x  -> let uu____2930 = f x in int_as_const r uu____2930) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2953 = f x y in int_as_const r uu____2953) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  -> fun x  -> let uu____2970 = f x in bool_as_const r uu____2970) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2993 = f x y in bool_as_const r uu____2993) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  -> let uu____3016 = f x y in string_as_const r uu____3016) in
  let list_of_string' rng s =
    let name l =
      let uu____3030 =
        let uu____3031 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            None in
        FStar_Syntax_Syntax.Tm_fvar uu____3031 in
      mk uu____3030 rng in
    let char_t = name FStar_Syntax_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____3041 =
      let uu____3043 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____3043 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____3041 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Const.exp_string s in
  let string_of_int1 rng i =
    let uu____3065 = FStar_Util.string_of_int i in
    string_as_const rng uu____3065 in
  let string_of_bool1 rng b =
    string_as_const rng (if b then "true" else "false") in
  let basic_ops =
    let uu____3084 =
      let uu____3094 =
        let uu____3104 =
          let uu____3114 =
            let uu____3124 =
              let uu____3134 =
                let uu____3144 =
                  let uu____3154 =
                    let uu____3164 =
                      let uu____3174 =
                        let uu____3184 =
                          let uu____3194 =
                            let uu____3204 =
                              let uu____3214 =
                                let uu____3224 =
                                  let uu____3234 =
                                    let uu____3244 =
                                      let uu____3253 =
                                        FStar_Syntax_Const.p2l
                                          ["FStar";
                                          "String";
                                          "list_of_string"] in
                                      (uu____3253, (Prims.parse_int "1"),
                                        (unary_op arg_as_string
                                           list_of_string')) in
                                    let uu____3259 =
                                      let uu____3269 =
                                        let uu____3278 =
                                          FStar_Syntax_Const.p2l
                                            ["FStar";
                                            "String";
                                            "string_of_list"] in
                                        (uu____3278, (Prims.parse_int "1"),
                                          (unary_op (arg_as_list arg_as_char)
                                             string_of_list')) in
                                      [uu____3269] in
                                    uu____3244 :: uu____3259 in
                                  (FStar_Syntax_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_bool string_of_bool1))
                                    :: uu____3234 in
                                (FStar_Syntax_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (unary_op arg_as_int string_of_int1)) ::
                                  uu____3224 in
                              (FStar_Syntax_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____3214 in
                            (FStar_Syntax_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____3204 in
                          (FStar_Syntax_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____3194 in
                        (FStar_Syntax_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____3184 in
                      (FStar_Syntax_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____3174 in
                    (FStar_Syntax_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
                      :: uu____3164 in
                  (FStar_Syntax_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____3154 in
                (FStar_Syntax_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____3144 in
              (FStar_Syntax_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____3134 in
            (FStar_Syntax_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____3124 in
          (FStar_Syntax_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____3114 in
        (FStar_Syntax_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____3104 in
      (FStar_Syntax_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____3094 in
    (FStar_Syntax_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____3084 in
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
            let uu____3578 =
              let uu____3587 = FStar_Syntax_Const.p2l ["FStar"; m; "add"] in
              (uu____3587, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  -> fun x  -> fun y  -> int_as_const r (x + y)))) in
            let uu____3596 =
              let uu____3606 =
                let uu____3615 = FStar_Syntax_Const.p2l ["FStar"; m; "sub"] in
                (uu____3615, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  -> fun x  -> fun y  -> int_as_const r (x - y)))) in
              let uu____3624 =
                let uu____3634 =
                  let uu____3643 = FStar_Syntax_Const.p2l ["FStar"; m; "mul"] in
                  (uu____3643, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  -> fun x  -> fun y  -> int_as_const r (x * y)))) in
                [uu____3634] in
              uu____3606 :: uu____3624 in
            uu____3578 :: uu____3596)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_bool rng args =
    match args with
    | (_typ,uu____3712)::(a1,uu____3714)::(a2,uu____3716)::[] ->
        let uu____3745 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3745 with
         | FStar_Syntax_Util.Equal  ->
             let uu____3747 =
               mk
                 (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_bool true)) rng in
             Some uu____3747
         | FStar_Syntax_Util.NotEqual  ->
             let uu____3752 =
               mk
                 (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_bool false)) rng in
             Some uu____3752
         | uu____3757 -> None)
    | uu____3758 -> failwith "Unexpected number of arguments" in
  let interp_prop r args =
    match args with
    | (_typ,_)::(a1,_)::(a2,_)::[]|(_typ,_)::_::(a1,_)::(a2,_)::[] ->
        let uu____3840 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3840 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___160_3844 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___160_3844.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___160_3844.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___160_3844.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___161_3851 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___161_3851.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___161_3851.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___161_3851.FStar_Syntax_Syntax.vars)
                })
         | uu____3856 -> None)
    | uu____3857 -> failwith "Unexpected number of arguments" in
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
      let uu____3868 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops cfg.steps) in
      if uu____3868
      then tm
      else
        (let uu____3870 = FStar_Syntax_Util.head_and_args tm in
         match uu____3870 with
         | (head1,args) ->
             let uu____3896 =
               let uu____3897 = FStar_Syntax_Util.un_uinst head1 in
               uu____3897.FStar_Syntax_Syntax.n in
             (match uu____3896 with
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____3901 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps in
                  (match uu____3901 with
                   | None  -> tm
                   | Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then tm
                       else
                         (let uu____3913 =
                            prim_step.interpretation
                              head1.FStar_Syntax_Syntax.pos args in
                          match uu____3913 with
                          | None  -> tm
                          | Some reduced -> reduced))
              | uu____3916 -> tm))
let reduce_equality:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___162_3923 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___162_3923.tcenv);
           delta_level = (uu___162_3923.delta_level);
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
        let uu___163_3945 = t in
        {
          FStar_Syntax_Syntax.n = (uu___163_3945.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___163_3945.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___163_3945.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid ->
            Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid ->
            Some false
        | uu____3964 -> None in
      let simplify arg = ((simp_t (Prims.fst arg)), arg) in
      let uu____3991 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps) in
      if uu____3991
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
             let uu____4031 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____4031
             then
               let uu____4032 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____4032 with
                | (Some (true ),_)::(_,(arg,_))::[]
                  |(_,(arg,_))::(Some (true ),_)::[] -> arg
                | (Some (false ),_)::_::[]|_::(Some (false ),_)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4198 -> tm)
             else
               (let uu____4208 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____4208
                then
                  let uu____4209 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____4209 with
                  | (Some (true ),_)::_::[]|_::(Some (true ),_)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),_)::(_,(arg,_))::[]
                    |(_,(arg,_))::(Some (false ),_)::[] -> arg
                  | uu____4375 -> tm
                else
                  (let uu____4385 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____4385
                   then
                     let uu____4386 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____4386 with
                     | _::(Some (true ),_)::[]|(Some (false ),_)::_::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____4475)::(uu____4476,(arg,uu____4478))::[]
                         -> arg
                     | uu____4519 -> tm
                   else
                     (let uu____4529 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____4529
                      then
                        let uu____4530 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____4530 with
                        | (Some (true ),uu____4563)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____4587)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____4611 -> tm
                      else
                        (let uu____4621 =
                           (FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Syntax_Const.forall_lid)
                             ||
                             (FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid) in
                         if uu____4621
                         then
                           match args with
                           | (t,_)::[]
                             |(_,Some (FStar_Syntax_Syntax.Implicit _))::
                             (t,_)::[] ->
                               let uu____4662 =
                                 let uu____4663 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____4663.FStar_Syntax_Syntax.n in
                               (match uu____4662 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____4666::[],body,uu____4668) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | Some (false ) ->
                                         w FStar_Syntax_Util.t_false
                                     | uu____4694 -> tm)
                                | uu____4696 -> tm)
                           | uu____4697 -> tm
                         else reduce_equality cfg tm))))
         | uu____4704 -> tm)
let is_norm_request hd1 args =
  let uu____4719 =
    let uu____4723 =
      let uu____4724 = FStar_Syntax_Util.un_uinst hd1 in
      uu____4724.FStar_Syntax_Syntax.n in
    (uu____4723, args) in
  match uu____4719 with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4729::uu____4730::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize_term
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4733::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize
  | uu____4735 -> false
let get_norm_request args =
  match args with
  | _::(tm,_)::[]|(tm,_)::[] -> tm
  | uu____4768 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___138_4775  ->
    match uu___138_4775 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.tk = uu____4777;
           FStar_Syntax_Syntax.pos = uu____4778;
           FStar_Syntax_Syntax.vars = uu____4779;_},uu____4780,uu____4781))::uu____4782
        -> true
    | uu____4788 -> false
let is_fstar_tactics_embed: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____4793 =
      let uu____4794 = FStar_Syntax_Util.un_uinst t in
      uu____4794.FStar_Syntax_Syntax.n in
    match uu____4793 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Syntax_Const.fstar_tactics_embed_lid
    | uu____4798 -> false
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
            (fun uu____4912  ->
               let uu____4913 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____4914 = FStar_Syntax_Print.term_to_string t1 in
               let uu____4915 =
                 let uu____4916 =
                   let uu____4918 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left Prims.fst uu____4918 in
                 stack_to_string uu____4916 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____4913
                 uu____4914 uu____4915);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____4930 ->
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
                  FStar_Syntax_Syntax.tk = uu____4962;
                  FStar_Syntax_Syntax.pos = uu____4963;
                  FStar_Syntax_Syntax.vars = uu____4964;_},uu____4965)
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Syntax_Const.fstar_tactics_embed_lid
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               is_fstar_tactics_embed hd1 ->
               let args1 = closures_as_args_delayed cfg env args in
               let t2 =
                 let uu___164_5005 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd1, args1));
                   FStar_Syntax_Syntax.tk =
                     (uu___164_5005.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___164_5005.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___164_5005.FStar_Syntax_Syntax.vars)
                 } in
               let t3 = reduce_primops cfg t2 in rebuild cfg env stack1 t3
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____5034 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____5034) && (is_norm_request hd1 args))
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
                 let uu___165_5047 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___165_5047.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___165_5047.primitive_steps)
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
                  FStar_Syntax_Syntax.tk = uu____5052;
                  FStar_Syntax_Syntax.pos = uu____5053;
                  FStar_Syntax_Syntax.vars = uu____5054;_},a1::a2::rest)
               ->
               let uu____5088 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____5088 with
                | (hd1,uu____5099) ->
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
                    (FStar_Const.Const_reflect uu____5154);
                  FStar_Syntax_Syntax.tk = uu____5155;
                  FStar_Syntax_Syntax.pos = uu____5156;
                  FStar_Syntax_Syntax.vars = uu____5157;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____5180 = FStar_List.tl stack1 in
               norm cfg env uu____5180 (Prims.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.tk = uu____5183;
                  FStar_Syntax_Syntax.pos = uu____5184;
                  FStar_Syntax_Syntax.vars = uu____5185;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____5208 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____5208 with
                | (reify_head,uu____5219) ->
                    let a1 =
                      let uu____5235 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (Prims.fst a) in
                      FStar_Syntax_Subst.compress uu____5235 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____5238);
                            FStar_Syntax_Syntax.tk = uu____5239;
                            FStar_Syntax_Syntax.pos = uu____5240;
                            FStar_Syntax_Syntax.vars = uu____5241;_},a2::[])
                         -> norm cfg env stack1 (Prims.fst a2)
                     | uu____5266 ->
                         let stack2 =
                           (App
                              (reify_head, None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____5274 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____5274
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____5281 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____5281
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____5284 =
                      let uu____5288 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____5288, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____5284 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___139_5297  ->
                         match uu___139_5297 with
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
                    let uu____5301 = FStar_Syntax_Syntax.range_of_fv f in
                    FStar_TypeChecker_Env.set_range cfg.tcenv uu____5301 in
                  let uu____5302 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  match uu____5302 with
                  | None  ->
                      (log cfg
                         (fun uu____5313  ->
                            FStar_Util.print "Tm_fvar case 2\n" []);
                       rebuild cfg env stack1 t1)
                  | Some (us,t2) ->
                      (log cfg
                         (fun uu____5319  ->
                            let uu____5320 =
                              FStar_Syntax_Print.term_to_string t0 in
                            let uu____5321 =
                              FStar_Syntax_Print.term_to_string t2 in
                            FStar_Util.print2 ">>> Unfolded %s to %s\n"
                              uu____5320 uu____5321);
                       (let n1 = FStar_List.length us in
                        if n1 > (Prims.parse_int "0")
                        then
                          match stack1 with
                          | (UnivArgs (us',uu____5328))::stack2 ->
                              let env1 =
                                FStar_All.pipe_right us'
                                  (FStar_List.fold_left
                                     (fun env1  -> fun u  -> (Univ u) :: env1)
                                     env) in
                              norm cfg env1 stack2 t2
                          | uu____5341 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack1 t2
                          | uu____5342 ->
                              let uu____5343 =
                                let uu____5344 =
                                  FStar_Syntax_Print.lid_to_string
                                    (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                FStar_Util.format1
                                  "Impossible: missing universe instantiation on %s"
                                  uu____5344 in
                              failwith uu____5343
                        else norm cfg env stack1 t2)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____5351 = lookup_bvar env x in
               (match uu____5351 with
                | Univ uu____5352 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____5367 = FStar_ST.read r in
                      (match uu____5367 with
                       | Some (env2,t') ->
                           (log cfg
                              (fun uu____5386  ->
                                 let uu____5387 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____5388 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____5387
                                   uu____5388);
                            (let uu____5389 =
                               let uu____5390 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____5390.FStar_Syntax_Syntax.n in
                             match uu____5389 with
                             | FStar_Syntax_Syntax.Tm_abs uu____5393 ->
                                 norm cfg env2 stack1 t'
                             | uu____5408 -> rebuild cfg env2 stack1 t'))
                       | None  -> norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____5441)::uu____5442 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____5447)::uu____5448 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____5454,uu____5455))::stack_rest ->
                    (match c with
                     | Univ uu____5458 -> norm cfg (c :: env) stack_rest t1
                     | uu____5459 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____5462::[] ->
                              (match lopt with
                               | None  when FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____5475  ->
                                         let uu____5476 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____5476);
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
                                           (fun uu___140_5490  ->
                                              match uu___140_5490 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____5491 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____5493  ->
                                         let uu____5494 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____5494);
                                    norm cfg (c :: env) stack_rest body)
                               | Some (FStar_Util.Inl lc) when
                                   FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                                   ->
                                   (log cfg
                                      (fun uu____5505  ->
                                         let uu____5506 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____5506);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____5507 when
                                   FStar_All.pipe_right cfg.steps
                                     (FStar_List.contains Reify)
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____5514 ->
                                   let cfg1 =
                                     let uu___166_5522 = cfg in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___166_5522.tcenv);
                                       delta_level =
                                         (uu___166_5522.delta_level);
                                       primitive_steps =
                                         (uu___166_5522.primitive_steps)
                                     } in
                                   let uu____5523 =
                                     closure_as_term cfg1 env t1 in
                                   rebuild cfg1 env stack1 uu____5523)
                          | uu____5524::tl1 ->
                              (log cfg
                                 (fun uu____5534  ->
                                    let uu____5535 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____5535);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___167_5559 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___167_5559.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____5572  ->
                          let uu____5573 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____5573);
                     norm cfg env stack2 t1)
                | (Debug _)::_
                  |(Meta _)::_|(Let _)::_|(App _)::_|(Abs _)::_|[] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____5584 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____5584
                    else
                      (let uu____5586 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____5586 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____5615 =
                                   let uu____5621 =
                                     let uu____5622 =
                                       let uu____5623 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____5623 in
                                     FStar_All.pipe_right uu____5622
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____5621
                                     (fun _0_30  -> FStar_Util.Inl _0_30) in
                                 FStar_All.pipe_right uu____5615
                                   (fun _0_31  -> Some _0_31)
                             | uu____5648 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____5662  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____5667  ->
                                 let uu____5668 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____5668);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___168_5678 = cfg in
                               let uu____5679 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___168_5678.steps);
                                 tcenv = (uu___168_5678.tcenv);
                                 delta_level = (uu___168_5678.delta_level);
                                 primitive_steps = uu____5679
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
                      (fun uu____5711  ->
                         fun stack2  ->
                           match uu____5711 with
                           | (a,aq) ->
                               let uu____5719 =
                                 let uu____5720 =
                                   let uu____5724 =
                                     let uu____5725 =
                                       let uu____5735 =
                                         FStar_Util.mk_ref None in
                                       (env, a, uu____5735, false) in
                                     Clos uu____5725 in
                                   (uu____5724, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____5720 in
                               uu____5719 :: stack2) args) in
               (log cfg
                  (fun uu____5757  ->
                     let uu____5758 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____5758);
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
                             ((let uu___169_5779 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___169_5779.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___169_5779.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____5780 ->
                      let uu____5783 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____5783)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____5786 = FStar_Syntax_Subst.open_term [(x, None)] f in
                  match uu____5786 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____5802 =
                          let uu____5803 =
                            let uu____5808 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___170_5809 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___170_5809.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___170_5809.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____5808) in
                          FStar_Syntax_Syntax.Tm_refine uu____5803 in
                        mk uu____5802 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____5822 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____5822
               else
                 (let uu____5824 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____5824 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____5830 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  -> fun uu____5836  -> Dummy :: env1)
                               env) in
                        norm_comp cfg uu____5830 c1 in
                      let t2 =
                        let uu____5843 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____5843 c2 in
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
                | uu____5900 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____5903  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____5916 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____5916
                        | FStar_Util.Inr c ->
                            let uu____5924 = norm_comp cfg env c in
                            FStar_Util.Inr uu____5924 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____5929 =
                        mk
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (t12, (tc1, tacopt1), l))
                          t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____5929)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____5980,{
                              FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                uu____5981;
                              FStar_Syntax_Syntax.lbunivs = uu____5982;
                              FStar_Syntax_Syntax.lbtyp = uu____5983;
                              FStar_Syntax_Syntax.lbeff = uu____5984;
                              FStar_Syntax_Syntax.lbdef = uu____5985;_}::uu____5986),uu____5987)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____6013 =
                 (let uu____6014 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____6014) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____6015 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____6015))) in
               if uu____6013
               then
                 let env1 =
                   let uu____6018 =
                     let uu____6019 =
                       let uu____6029 = FStar_Util.mk_ref None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____6029,
                         false) in
                     Clos uu____6019 in
                   uu____6018 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____6053 =
                    let uu____6056 =
                      let uu____6057 =
                        let uu____6058 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____6058
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____6057] in
                    FStar_Syntax_Subst.open_term uu____6056 body in
                  match uu____6053 with
                  | (bs,body1) ->
                      let lb1 =
                        let uu___171_6064 = lb in
                        let uu____6065 =
                          let uu____6068 =
                            let uu____6069 = FStar_List.hd bs in
                            FStar_All.pipe_right uu____6069 Prims.fst in
                          FStar_All.pipe_right uu____6068
                            (fun _0_32  -> FStar_Util.Inl _0_32) in
                        let uu____6078 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____6081 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = uu____6065;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___171_6064.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____6078;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___171_6064.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____6081
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____6091  -> Dummy :: env1)
                             env) in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____6107 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____6107
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____6120 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____6142  ->
                        match uu____6142 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____6181 =
                                let uu___172_6182 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___172_6182.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___172_6182.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____6181 in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos in
                            let memo = FStar_Util.mk_ref None in
                            let rec_env1 = (Clos (env, fix_f_i, memo, true))
                              :: rec_env in
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1")))) (Prims.snd lbs)
                   (env, [], (Prims.parse_int "0")) in
               (match uu____6120 with
                | (rec_env,memos,uu____6242) ->
                    let uu____6257 =
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
                             let uu____6299 =
                               let uu____6300 =
                                 let uu____6310 = FStar_Util.mk_ref None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____6310, false) in
                               Clos uu____6300 in
                             uu____6299 :: env1) (Prims.snd lbs) env in
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
                             FStar_Syntax_Syntax.tk = uu____6348;
                             FStar_Syntax_Syntax.pos = uu____6349;
                             FStar_Syntax_Syntax.vars = uu____6350;_},uu____6351,uu____6352))::uu____6353
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____6359 -> false in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____6366 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____6366
                        then
                          let uu___173_6367 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___173_6367.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps = (uu___173_6367.primitive_steps)
                          }
                        else
                          (let uu___174_6369 = cfg in
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___174_6369.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta];
                             primitive_steps =
                               (uu___174_6369.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____6371 =
                         let uu____6372 = FStar_Syntax_Subst.compress head1 in
                         uu____6372.FStar_Syntax_Syntax.n in
                       match uu____6371 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____6386 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____6386 with
                            | (uu____6387,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____6391 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____6398 =
                                         let uu____6399 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____6399.FStar_Syntax_Syntax.n in
                                       match uu____6398 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____6404,uu____6405))
                                           ->
                                           let uu____6414 =
                                             let uu____6415 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____6415.FStar_Syntax_Syntax.n in
                                           (match uu____6414 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____6420,msrc,uu____6422))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____6431 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                Some uu____6431
                                            | uu____6432 -> None)
                                       | uu____6433 -> None in
                                     let uu____6434 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____6434 with
                                      | Some e ->
                                          let lb1 =
                                            let uu___175_6438 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___175_6438.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___175_6438.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___175_6438.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Syntax_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____6439 =
                                            FStar_List.tl stack1 in
                                          let uu____6440 =
                                            let uu____6441 =
                                              let uu____6444 =
                                                let uu____6445 =
                                                  let uu____6453 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____6453) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____6445 in
                                              FStar_Syntax_Syntax.mk
                                                uu____6444 in
                                            uu____6441 None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____6439 uu____6440
                                      | None  ->
                                          let uu____6470 =
                                            let uu____6471 = is_return body in
                                            match uu____6471 with
                                            | Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____6474;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____6475;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____6476;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____6481 -> false in
                                          if uu____6470
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
                                               let uu____6501 =
                                                 let uu____6504 =
                                                   let uu____6505 =
                                                     let uu____6520 =
                                                       let uu____6522 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____6522] in
                                                     (uu____6520, body1,
                                                       (Some
                                                          (FStar_Util.Inr
                                                             (m1, [])))) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____6505 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____6504 in
                                               uu____6501 None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____6555 =
                                                 let uu____6556 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____6556.FStar_Syntax_Syntax.n in
                                               match uu____6555 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____6562::uu____6563::[])
                                                   ->
                                                   let uu____6569 =
                                                     let uu____6572 =
                                                       let uu____6573 =
                                                         let uu____6578 =
                                                           let uu____6580 =
                                                             let uu____6581 =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____6581 in
                                                           let uu____6582 =
                                                             let uu____6584 =
                                                               let uu____6585
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____6585 in
                                                             [uu____6584] in
                                                           uu____6580 ::
                                                             uu____6582 in
                                                         (bind1, uu____6578) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____6573 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____6572 in
                                                   uu____6569 None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____6597 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____6603 =
                                                 let uu____6606 =
                                                   let uu____6607 =
                                                     let uu____6617 =
                                                       let uu____6619 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____6620 =
                                                         let uu____6622 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____6623 =
                                                           let uu____6625 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____6626 =
                                                             let uu____6628 =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____6629 =
                                                               let uu____6631
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____6632
                                                                 =
                                                                 let uu____6634
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____6634] in
                                                               uu____6631 ::
                                                                 uu____6632 in
                                                             uu____6628 ::
                                                               uu____6629 in
                                                           uu____6625 ::
                                                             uu____6626 in
                                                         uu____6622 ::
                                                           uu____6623 in
                                                       uu____6619 ::
                                                         uu____6620 in
                                                     (bind_inst, uu____6617) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____6607 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____6606 in
                                               uu____6603 None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____6646 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____6646 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____6664 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____6664 with
                            | (uu____6665,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____6688 =
                                        let uu____6689 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____6689.FStar_Syntax_Syntax.n in
                                      match uu____6688 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____6695) -> t4
                                      | uu____6700 -> head2 in
                                    let uu____6701 =
                                      let uu____6702 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____6702.FStar_Syntax_Syntax.n in
                                    match uu____6701 with
                                    | FStar_Syntax_Syntax.Tm_fvar x -> Some x
                                    | uu____6707 -> None in
                                  let uu____6708 = maybe_extract_fv head2 in
                                  match uu____6708 with
                                  | Some x when
                                      let uu____6714 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____6714
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____6718 =
                                          maybe_extract_fv head3 in
                                        match uu____6718 with
                                        | Some uu____6721 -> Some true
                                        | uu____6722 -> Some false in
                                      (head3, action_unfolded)
                                  | uu____6725 -> (head2, None) in
                                ((let is_arg_impure uu____6736 =
                                    match uu____6736 with
                                    | (e,q) ->
                                        let uu____6741 =
                                          let uu____6742 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____6742.FStar_Syntax_Syntax.n in
                                        (match uu____6741 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____6757 -> false) in
                                  let uu____6758 =
                                    let uu____6759 =
                                      let uu____6763 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____6763 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____6759 in
                                  if uu____6758
                                  then
                                    let uu____6766 =
                                      let uu____6767 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____6767 in
                                    failwith uu____6766
                                  else ());
                                 (let uu____6769 =
                                    maybe_unfold_action head_app in
                                  match uu____6769 with
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
                                      let uu____6804 = FStar_List.tl stack1 in
                                      norm cfg env uu____6804 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____6818 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____6818 in
                           let uu____6819 = FStar_List.tl stack1 in
                           norm cfg env uu____6819 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____6902  ->
                                     match uu____6902 with
                                     | (pat,wopt,tm) ->
                                         let uu____6940 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____6940))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____6966 = FStar_List.tl stack1 in
                           norm cfg env uu____6966 tm
                       | uu____6967 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.tk = uu____6976;
                             FStar_Syntax_Syntax.pos = uu____6977;
                             FStar_Syntax_Syntax.vars = uu____6978;_},uu____6979,uu____6980))::uu____6981
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____6987 -> false in
                    if should_reify
                    then
                      let uu____6988 = FStar_List.tl stack1 in
                      let uu____6989 =
                        let uu____6990 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____6990 in
                      norm cfg env uu____6988 uu____6989
                    else
                      (let uu____6992 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____6992
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___176_6998 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___176_6998.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___176_6998.primitive_steps)
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
                | uu____7004 ->
                    (match stack1 with
                     | uu____7005::uu____7006 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____7010)
                              -> norm cfg env ((Meta (m, r)) :: stack1) head1
                          | FStar_Syntax_Syntax.Meta_pattern args ->
                              let args1 = norm_pattern_args cfg env args in
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_pattern args1),
                                      (t1.FStar_Syntax_Syntax.pos))) ::
                                stack1) head1
                          | uu____7025 -> norm cfg env stack1 head1)
                     | [] ->
                         let head2 = norm cfg env [] head1 in
                         let m1 =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               let uu____7035 =
                                 norm_pattern_args cfg env args in
                               FStar_Syntax_Syntax.Meta_pattern uu____7035
                           | uu____7042 -> m in
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
              let uu____7054 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____7054 with
              | (uu____7055,return_repr) ->
                  let return_inst =
                    let uu____7062 =
                      let uu____7063 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____7063.FStar_Syntax_Syntax.n in
                    match uu____7062 with
                    | FStar_Syntax_Syntax.Tm_uinst (return_tm,uu____7069::[])
                        ->
                        let uu____7075 =
                          let uu____7078 =
                            let uu____7079 =
                              let uu____7084 =
                                let uu____7086 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____7086] in
                              (return_tm, uu____7084) in
                            FStar_Syntax_Syntax.Tm_uinst uu____7079 in
                          FStar_Syntax_Syntax.mk uu____7078 in
                        uu____7075 None e.FStar_Syntax_Syntax.pos
                    | uu____7098 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____7101 =
                    let uu____7104 =
                      let uu____7105 =
                        let uu____7115 =
                          let uu____7117 = FStar_Syntax_Syntax.as_arg t in
                          let uu____7118 =
                            let uu____7120 = FStar_Syntax_Syntax.as_arg e in
                            [uu____7120] in
                          uu____7117 :: uu____7118 in
                        (return_inst, uu____7115) in
                      FStar_Syntax_Syntax.Tm_app uu____7105 in
                    FStar_Syntax_Syntax.mk uu____7104 in
                  uu____7101 None e.FStar_Syntax_Syntax.pos
            else
              (let uu____7133 = FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____7133 with
               | None  ->
                   let uu____7135 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____7135
               | Some
                   { FStar_TypeChecker_Env.msource = uu____7136;
                     FStar_TypeChecker_Env.mtarget = uu____7137;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____7138;
                         FStar_TypeChecker_Env.mlift_term = None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | Some
                   { FStar_TypeChecker_Env.msource = uu____7149;
                     FStar_TypeChecker_Env.mtarget = uu____7150;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____7151;
                         FStar_TypeChecker_Env.mlift_term = Some lift;_};_}
                   ->
                   let uu____7169 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____7169)
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
                (fun uu____7199  ->
                   match uu____7199 with
                   | (a,imp) ->
                       let uu____7206 = norm cfg env [] a in
                       (uu____7206, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___177_7221 = comp1 in
            let uu____7224 =
              let uu____7225 =
                let uu____7231 = norm cfg env [] t in
                let uu____7232 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____7231, uu____7232) in
              FStar_Syntax_Syntax.Total uu____7225 in
            {
              FStar_Syntax_Syntax.n = uu____7224;
              FStar_Syntax_Syntax.tk = (uu___177_7221.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___177_7221.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___177_7221.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___178_7247 = comp1 in
            let uu____7250 =
              let uu____7251 =
                let uu____7257 = norm cfg env [] t in
                let uu____7258 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____7257, uu____7258) in
              FStar_Syntax_Syntax.GTotal uu____7251 in
            {
              FStar_Syntax_Syntax.n = uu____7250;
              FStar_Syntax_Syntax.tk = (uu___178_7247.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___178_7247.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___178_7247.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____7289  ->
                      match uu____7289 with
                      | (a,i) ->
                          let uu____7296 = norm cfg env [] a in
                          (uu____7296, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___141_7301  ->
                      match uu___141_7301 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____7305 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____7305
                      | f -> f)) in
            let uu___179_7309 = comp1 in
            let uu____7312 =
              let uu____7313 =
                let uu___180_7314 = ct in
                let uu____7315 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____7316 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____7319 = norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____7315;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___180_7314.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____7316;
                  FStar_Syntax_Syntax.effect_args = uu____7319;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____7313 in
            {
              FStar_Syntax_Syntax.n = uu____7312;
              FStar_Syntax_Syntax.tk = (uu___179_7309.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___179_7309.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___179_7309.FStar_Syntax_Syntax.vars)
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
            (let uu___181_7336 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___181_7336.tcenv);
               delta_level = (uu___181_7336.delta_level);
               primitive_steps = (uu___181_7336.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____7341 = norm1 t in
          FStar_Syntax_Util.non_informative uu____7341 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____7344 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___182_7358 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.tk = (uu___182_7358.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___182_7358.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___182_7358.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____7368 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____7368
            then
              let ct1 =
                match downgrade_ghost_effect_name
                        ct.FStar_Syntax_Syntax.effect_name
                with
                | Some pure_eff ->
                    let uu___183_7373 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___183_7373.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___183_7373.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___183_7373.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___183_7373.FStar_Syntax_Syntax.flags)
                    }
                | None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___184_7375 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___184_7375.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Syntax_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___184_7375.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___184_7375.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___184_7375.FStar_Syntax_Syntax.flags)
                    } in
              let uu___185_7376 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.tk =
                  (uu___185_7376.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___185_7376.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___185_7376.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____7382 -> c
and norm_binder:
  cfg ->
    env ->
      FStar_Syntax_Syntax.binder ->
        (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  =
  fun cfg  ->
    fun env  ->
      fun uu____7385  ->
        match uu____7385 with
        | (x,imp) ->
            let uu____7388 =
              let uu___186_7389 = x in
              let uu____7390 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___186_7389.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___186_7389.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____7390
              } in
            (uu____7388, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____7396 =
          FStar_List.fold_left
            (fun uu____7403  ->
               fun b  ->
                 match uu____7403 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____7396 with | (nbs,uu____7420) -> FStar_List.rev nbs
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
            let uu____7437 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
            if uu____7437
            then
              let t = norm cfg env [] lc.FStar_Syntax_Syntax.res_typ in
              let uu____7442 = FStar_Syntax_Util.is_total_lcomp lc in
              (if uu____7442
               then
                 let uu____7446 =
                   let uu____7449 =
                     let uu____7450 =
                       let uu____7453 = FStar_Syntax_Syntax.mk_Total t in
                       FStar_Syntax_Util.comp_set_flags uu____7453 flags in
                     FStar_Syntax_Util.lcomp_of_comp uu____7450 in
                   FStar_Util.Inl uu____7449 in
                 Some uu____7446
               else
                 (let uu____7457 =
                    let uu____7460 =
                      let uu____7461 =
                        let uu____7464 = FStar_Syntax_Syntax.mk_GTotal t in
                        FStar_Syntax_Util.comp_set_flags uu____7464 flags in
                      FStar_Syntax_Util.lcomp_of_comp uu____7461 in
                    FStar_Util.Inl uu____7460 in
                  Some uu____7457))
            else
              Some
                (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags))
        | uu____7477 -> lopt
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
              ((let uu____7489 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____7489
                then
                  let uu____7490 = FStar_Syntax_Print.term_to_string tm in
                  let uu____7491 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2 "Normalized %s to %s\n" uu____7490
                    uu____7491
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___187_7502 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___187_7502.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____7522  ->
                    let uu____7523 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____7523);
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
              let uu____7560 =
                let uu___188_7561 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___188_7561.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___188_7561.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___188_7561.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____7560
          | (Arg (Univ _,_,_))::_|(Arg (Dummy ,_,_))::_ ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____7583),aq,r))::stack2 ->
              (log cfg
                 (fun uu____7599  ->
                    let uu____7600 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____7600);
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
                 (let uu____7611 = FStar_ST.read m in
                  match uu____7611 with
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
                  | Some (uu____7637,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq) None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.extend_app head1 (t, aq) None r in
              let uu____7659 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____7659
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____7666  ->
                    let uu____7667 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____7667);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____7672 =
                  log cfg
                    (fun uu____7674  ->
                       let uu____7675 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____7676 =
                         let uu____7677 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____7684  ->
                                   match uu____7684 with
                                   | (p,uu____7690,uu____7691) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____7677
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____7675 uu____7676);
                  (let whnf = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___142_7701  ->
                               match uu___142_7701 with
                               | FStar_TypeChecker_Env.Inlining 
                                 |FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____7702 -> false)) in
                     let steps' =
                       let uu____7705 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____7705
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___189_7708 = cfg in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___189_7708.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___189_7708.primitive_steps)
                     } in
                   let norm_or_whnf env2 t1 =
                     if whnf
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____7742 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_disj [] ->
                         failwith "Impossible"
                     | FStar_Syntax_Syntax.Pat_disj (hd1::tl1) ->
                         let uu____7762 = norm_pat env2 hd1 in
                         (match uu____7762 with
                          | (hd2,env') ->
                              let tl2 =
                                FStar_All.pipe_right tl1
                                  (FStar_List.map
                                     (fun p1  ->
                                        let uu____7798 = norm_pat env2 p1 in
                                        Prims.fst uu____7798)) in
                              ((let uu___190_7810 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_disj (hd2 ::
                                       tl2));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___190_7810.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___190_7810.FStar_Syntax_Syntax.p)
                                }), env'))
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____7827 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____7861  ->
                                   fun uu____7862  ->
                                     match (uu____7861, uu____7862) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____7927 = norm_pat env3 p1 in
                                         (match uu____7927 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____7827 with
                          | (pats1,env3) ->
                              ((let uu___191_7993 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___191_7993.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___191_7993.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___192_8007 = x in
                           let uu____8008 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___192_8007.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___192_8007.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____8008
                           } in
                         ((let uu___193_8014 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___193_8014.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___193_8014.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___194_8019 = x in
                           let uu____8020 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___194_8019.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___194_8019.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____8020
                           } in
                         ((let uu___195_8026 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___195_8026.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___195_8026.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___196_8036 = x in
                           let uu____8037 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___196_8036.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___196_8036.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____8037
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___197_8044 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.ty =
                               (uu___197_8044.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___197_8044.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf -> branches
                     | uu____8048 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____8051 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____8051 with
                                 | (p,wopt,e) ->
                                     let uu____8069 = norm_pat env1 p in
                                     (match uu____8069 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | None  -> None
                                            | Some w ->
                                                let uu____8093 =
                                                  norm_or_whnf env2 w in
                                                Some uu____8093 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____8098 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____8098) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____8108) -> is_cons h
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
                  | uu____8119 -> false in
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
                  let uu____8218 = FStar_Syntax_Util.head_and_args scrutinee2 in
                  match uu____8218 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_disj ps ->
                           let mopt =
                             FStar_Util.find_map ps
                               (fun p1  ->
                                  let m = matches_pat scrutinee2 p1 in
                                  match m with
                                  | FStar_Util.Inl uu____8275 -> Some m
                                  | FStar_Util.Inr (true ) -> Some m
                                  | FStar_Util.Inr (false ) -> None) in
                           (match mopt with
                            | None  -> FStar_Util.Inr false
                            | Some m -> m)
                       | FStar_Syntax_Syntax.Pat_var _
                         |FStar_Syntax_Syntax.Pat_wild _ ->
                           FStar_Util.Inl [scrutinee2]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____8306 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____8318 ->
                                let uu____8319 =
                                  let uu____8320 = is_cons head1 in
                                  Prims.op_Negation uu____8320 in
                                FStar_Util.Inr uu____8319)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____8334 =
                             let uu____8335 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____8335.FStar_Syntax_Syntax.n in
                           (match uu____8334 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____8342 ->
                                let uu____8343 =
                                  let uu____8344 = is_cons head1 in
                                  Prims.op_Negation uu____8344 in
                                FStar_Util.Inr uu____8343))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____8378)::rest_a,(p1,uu____8381)::rest_p) ->
                      let uu____8409 = matches_pat t1 p1 in
                      (match uu____8409 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____8423 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____8494 = matches_pat scrutinee1 p1 in
                      (match uu____8494 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____8504  ->
                                 let uu____8505 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____8506 =
                                   let uu____8507 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____8507
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____8505 uu____8506);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____8516 =
                                        let uu____8517 =
                                          let uu____8527 =
                                            FStar_Util.mk_ref (Some ([], t1)) in
                                          ([], t1, uu____8527, false) in
                                        Clos uu____8517 in
                                      uu____8516 :: env2) env1 s in
                             let uu____8550 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____8550))) in
                let uu____8551 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____8551
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___143_8565  ->
                match uu___143_8565 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | uu____8568 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____8572 -> d in
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
            let uu___198_8592 = config s e in
            {
              steps = (uu___198_8592.steps);
              tcenv = (uu___198_8592.tcenv);
              delta_level = (uu___198_8592.delta_level);
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
      fun t  -> let uu____8611 = config s e in norm_comp uu____8611 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  -> let uu____8618 = config [] env in norm_universe uu____8618 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun c  ->
      let uu____8625 = config [] env in ghost_to_pure_aux uu____8625 [] c
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
        let uu____8637 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____8637 in
      let uu____8638 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____8638
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | Some pure_eff ->
            let uu___199_8640 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___199_8640.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___199_8640.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____8641  ->
                    let uu____8642 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____8642))
            }
        | None  -> lc
      else lc
let term_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun env  ->
    fun t  ->
      let uu____8650 = normalize [AllowUnboundUniverses] env t in
      FStar_Syntax_Print.term_to_string uu____8650
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let uu____8657 =
        let uu____8658 = config [AllowUnboundUniverses] env in
        norm_comp uu____8658 [] c in
      FStar_Syntax_Print.comp_to_string uu____8657
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
                   let uu____8695 =
                     let uu____8696 =
                       let uu____8701 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____8701) in
                     FStar_Syntax_Syntax.Tm_refine uu____8696 in
                   mk uu____8695 t01.FStar_Syntax_Syntax.pos
               | uu____8706 -> t2)
          | uu____8707 -> t2 in
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
        let uu____8723 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____8723 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____8739 ->
                 let uu____8743 = FStar_Syntax_Util.abs_formals e in
                 (match uu____8743 with
                  | (actuals,uu____8754,uu____8755) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____8777 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____8777 with
                         | (binders,args) ->
                             let uu____8787 =
                               (FStar_Syntax_Syntax.mk_Tm_app e args) None
                                 e.FStar_Syntax_Syntax.pos in
                             let uu____8792 =
                               let uu____8799 =
                                 FStar_All.pipe_right
                                   (FStar_Syntax_Util.lcomp_of_comp c)
                                   (fun _0_33  -> FStar_Util.Inl _0_33) in
                               FStar_All.pipe_right uu____8799
                                 (fun _0_34  -> Some _0_34) in
                             FStar_Syntax_Util.abs binders uu____8787
                               uu____8792)))
let eta_expand:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____8835 =
        let uu____8839 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
        (uu____8839, (t.FStar_Syntax_Syntax.n)) in
      match uu____8835 with
      | (Some sort,uu____8846) ->
          let uu____8848 = mk sort t.FStar_Syntax_Syntax.pos in
          eta_expand_with_type env t uu____8848
      | (uu____8849,FStar_Syntax_Syntax.Tm_name x) ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____8853 ->
          let uu____8857 = FStar_Syntax_Util.head_and_args t in
          (match uu____8857 with
           | (head1,args) ->
               let uu____8883 =
                 let uu____8884 = FStar_Syntax_Subst.compress head1 in
                 uu____8884.FStar_Syntax_Syntax.n in
               (match uu____8883 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____8887,thead) ->
                    let uu____8901 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____8901 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____8932 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___200_8936 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___200_8936.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___200_8936.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___200_8936.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___200_8936.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___200_8936.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___200_8936.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ = None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___200_8936.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___200_8936.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___200_8936.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___200_8936.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___200_8936.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___200_8936.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___200_8936.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___200_8936.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___200_8936.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___200_8936.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___200_8936.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___200_8936.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___200_8936.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___200_8936.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___200_8936.FStar_TypeChecker_Env.qname_and_index)
                                 }) t in
                            match uu____8932 with
                            | (uu____8937,ty,uu____8939) ->
                                eta_expand_with_type env t ty))
                | uu____8940 ->
                    let uu____8941 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___201_8945 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___201_8945.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___201_8945.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___201_8945.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___201_8945.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___201_8945.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___201_8945.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ = None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___201_8945.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___201_8945.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___201_8945.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___201_8945.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___201_8945.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___201_8945.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___201_8945.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___201_8945.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___201_8945.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___201_8945.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___201_8945.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___201_8945.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___201_8945.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___201_8945.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___201_8945.FStar_TypeChecker_Env.qname_and_index)
                         }) t in
                    (match uu____8941 with
                     | (uu____8946,ty,uu____8948) ->
                         eta_expand_with_type env t ty)))