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
               (let uu___160_3730 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___160_3730.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___160_3730.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___160_3730.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___161_3737 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___161_3737.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___161_3737.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___161_3737.FStar_Syntax_Syntax.vars)
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
        (let uu___162_3809 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___162_3809.tcenv);
           delta_level = (uu___162_3809.delta_level);
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
        let uu___163_3831 = t in
        {
          FStar_Syntax_Syntax.n = (uu___163_3831.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___163_3831.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___163_3831.FStar_Syntax_Syntax.vars)
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
  fun uu___138_4661  ->
    match uu___138_4661 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.tk = uu____4663;
           FStar_Syntax_Syntax.pos = uu____4664;
           FStar_Syntax_Syntax.vars = uu____4665;_},uu____4666,uu____4667))::uu____4668
        -> true
    | uu____4674 -> false
let is_fstar_tactics_embed: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____4679 =
      let uu____4680 = FStar_Syntax_Util.un_uinst t in
      uu____4680.FStar_Syntax_Syntax.n in
    match uu____4679 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Syntax_Const.fstar_tactics_embed_lid
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
            (fun uu____4798  ->
               let uu____4799 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____4800 = FStar_Syntax_Print.term_to_string t1 in
               let uu____4801 =
                 let uu____4802 =
                   let uu____4804 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left Prims.fst uu____4804 in
                 stack_to_string uu____4802 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____4799
                 uu____4800 uu____4801);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____4816 ->
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
                  FStar_Syntax_Syntax.tk = uu____4848;
                  FStar_Syntax_Syntax.pos = uu____4849;
                  FStar_Syntax_Syntax.vars = uu____4850;_},uu____4851)
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Syntax_Const.fstar_tactics_embed_lid
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               is_fstar_tactics_embed hd1 ->
               let args1 = closures_as_args_delayed cfg env args in
               let t2 =
                 let uu___164_4891 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd1, args1));
                   FStar_Syntax_Syntax.tk =
                     (uu___164_4891.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___164_4891.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___164_4891.FStar_Syntax_Syntax.vars)
                 } in
               let t3 = reduce_primops cfg t2 in rebuild cfg env stack1 t3
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____4920 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____4920) && (is_norm_request hd1 args))
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
                 let uu___165_4933 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___165_4933.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___165_4933.primitive_steps)
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
                  FStar_Syntax_Syntax.tk = uu____4938;
                  FStar_Syntax_Syntax.pos = uu____4939;
                  FStar_Syntax_Syntax.vars = uu____4940;_},a1::a2::rest)
               ->
               let uu____4974 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____4974 with
                | (hd1,uu____4985) ->
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
                    (FStar_Const.Const_reflect uu____5040);
                  FStar_Syntax_Syntax.tk = uu____5041;
                  FStar_Syntax_Syntax.pos = uu____5042;
                  FStar_Syntax_Syntax.vars = uu____5043;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____5066 = FStar_List.tl stack1 in
               norm cfg env uu____5066 (Prims.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.tk = uu____5069;
                  FStar_Syntax_Syntax.pos = uu____5070;
                  FStar_Syntax_Syntax.vars = uu____5071;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____5094 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____5094 with
                | (reify_head,uu____5105) ->
                    let a1 =
                      let uu____5121 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (Prims.fst a) in
                      FStar_Syntax_Subst.compress uu____5121 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____5124);
                            FStar_Syntax_Syntax.tk = uu____5125;
                            FStar_Syntax_Syntax.pos = uu____5126;
                            FStar_Syntax_Syntax.vars = uu____5127;_},a2::[])
                         -> norm cfg env stack1 (Prims.fst a2)
                     | uu____5152 ->
                         let stack2 =
                           (App
                              (reify_head, None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____5160 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____5160
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____5167 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____5167
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____5170 =
                      let uu____5174 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____5174, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____5170 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___139_5183  ->
                         match uu___139_5183 with
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
                    let uu____5187 = FStar_Syntax_Syntax.range_of_fv f in
                    FStar_TypeChecker_Env.set_range cfg.tcenv uu____5187 in
                  let uu____5188 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  match uu____5188 with
                  | None  ->
                      (log cfg
                         (fun uu____5199  ->
                            FStar_Util.print "Tm_fvar case 2\n" []);
                       rebuild cfg env stack1 t1)
                  | Some (us,t2) ->
                      (log cfg
                         (fun uu____5205  ->
                            let uu____5206 =
                              FStar_Syntax_Print.term_to_string t0 in
                            let uu____5207 =
                              FStar_Syntax_Print.term_to_string t2 in
                            FStar_Util.print2 ">>> Unfolded %s to %s\n"
                              uu____5206 uu____5207);
                       (let n1 = FStar_List.length us in
                        if n1 > (Prims.parse_int "0")
                        then
                          match stack1 with
                          | (UnivArgs (us',uu____5214))::stack2 ->
                              let env1 =
                                FStar_All.pipe_right us'
                                  (FStar_List.fold_left
                                     (fun env1  -> fun u  -> (Univ u) :: env1)
                                     env) in
                              norm cfg env1 stack2 t2
                          | uu____5227 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack1 t2
                          | uu____5228 ->
                              let uu____5229 =
                                let uu____5230 =
                                  FStar_Syntax_Print.lid_to_string
                                    (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                FStar_Util.format1
                                  "Impossible: missing universe instantiation on %s"
                                  uu____5230 in
                              failwith uu____5229
                        else norm cfg env stack1 t2)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____5237 = lookup_bvar env x in
               (match uu____5237 with
                | Univ uu____5238 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____5253 = FStar_ST.read r in
                      (match uu____5253 with
                       | Some (env2,t') ->
                           (log cfg
                              (fun uu____5272  ->
                                 let uu____5273 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____5274 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____5273
                                   uu____5274);
                            (let uu____5275 =
                               let uu____5276 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____5276.FStar_Syntax_Syntax.n in
                             match uu____5275 with
                             | FStar_Syntax_Syntax.Tm_abs uu____5279 ->
                                 norm cfg env2 stack1 t'
                             | uu____5294 -> rebuild cfg env2 stack1 t'))
                       | None  -> norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____5327)::uu____5328 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____5333)::uu____5334 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____5340,uu____5341))::stack_rest ->
                    (match c with
                     | Univ uu____5344 -> norm cfg (c :: env) stack_rest t1
                     | uu____5345 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____5348::[] ->
                              (match lopt with
                               | None  when FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____5361  ->
                                         let uu____5362 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____5362);
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
                                           (fun uu___140_5376  ->
                                              match uu___140_5376 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____5377 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____5379  ->
                                         let uu____5380 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____5380);
                                    norm cfg (c :: env) stack_rest body)
                               | Some (FStar_Util.Inl lc) when
                                   FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                                   ->
                                   (log cfg
                                      (fun uu____5391  ->
                                         let uu____5392 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____5392);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____5393 when
                                   FStar_All.pipe_right cfg.steps
                                     (FStar_List.contains Reify)
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____5400 ->
                                   let cfg1 =
                                     let uu___166_5408 = cfg in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___166_5408.tcenv);
                                       delta_level =
                                         (uu___166_5408.delta_level);
                                       primitive_steps =
                                         (uu___166_5408.primitive_steps)
                                     } in
                                   let uu____5409 =
                                     closure_as_term cfg1 env t1 in
                                   rebuild cfg1 env stack1 uu____5409)
                          | uu____5410::tl1 ->
                              (log cfg
                                 (fun uu____5420  ->
                                    let uu____5421 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____5421);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___167_5445 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___167_5445.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____5458  ->
                          let uu____5459 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____5459);
                     norm cfg env stack2 t1)
                | (Debug _)::_
                  |(Meta _)::_|(Let _)::_|(App _)::_|(Abs _)::_|[] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____5470 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____5470
                    else
                      (let uu____5472 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____5472 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____5501 =
                                   let uu____5507 =
                                     let uu____5508 =
                                       let uu____5509 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____5509 in
                                     FStar_All.pipe_right uu____5508
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____5507
                                     (fun _0_30  -> FStar_Util.Inl _0_30) in
                                 FStar_All.pipe_right uu____5501
                                   (fun _0_31  -> Some _0_31)
                             | uu____5534 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____5548  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____5553  ->
                                 let uu____5554 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____5554);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___168_5564 = cfg in
                               let uu____5565 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___168_5564.steps);
                                 tcenv = (uu___168_5564.tcenv);
                                 delta_level = (uu___168_5564.delta_level);
                                 primitive_steps = uu____5565
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
                      (fun uu____5597  ->
                         fun stack2  ->
                           match uu____5597 with
                           | (a,aq) ->
                               let uu____5605 =
                                 let uu____5606 =
                                   let uu____5610 =
                                     let uu____5611 =
                                       let uu____5621 =
                                         FStar_Util.mk_ref None in
                                       (env, a, uu____5621, false) in
                                     Clos uu____5611 in
                                   (uu____5610, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____5606 in
                               uu____5605 :: stack2) args) in
               (log cfg
                  (fun uu____5643  ->
                     let uu____5644 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____5644);
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
                             ((let uu___169_5665 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___169_5665.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___169_5665.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____5666 ->
                      let uu____5669 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____5669)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____5672 = FStar_Syntax_Subst.open_term [(x, None)] f in
                  match uu____5672 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____5688 =
                          let uu____5689 =
                            let uu____5694 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___170_5695 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___170_5695.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___170_5695.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____5694) in
                          FStar_Syntax_Syntax.Tm_refine uu____5689 in
                        mk uu____5688 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____5708 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____5708
               else
                 (let uu____5710 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____5710 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____5716 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  -> fun uu____5722  -> Dummy :: env1)
                               env) in
                        norm_comp cfg uu____5716 c1 in
                      let t2 =
                        let uu____5729 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____5729 c2 in
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
                | uu____5786 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____5789  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____5802 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____5802
                        | FStar_Util.Inr c ->
                            let uu____5810 = norm_comp cfg env c in
                            FStar_Util.Inr uu____5810 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____5815 =
                        mk
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (t12, (tc1, tacopt1), l))
                          t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____5815)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____5866,{
                              FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                uu____5867;
                              FStar_Syntax_Syntax.lbunivs = uu____5868;
                              FStar_Syntax_Syntax.lbtyp = uu____5869;
                              FStar_Syntax_Syntax.lbeff = uu____5870;
                              FStar_Syntax_Syntax.lbdef = uu____5871;_}::uu____5872),uu____5873)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____5899 =
                 (let uu____5900 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____5900) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____5901 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____5901))) in
               if uu____5899
               then
                 let env1 =
                   let uu____5904 =
                     let uu____5905 =
                       let uu____5915 = FStar_Util.mk_ref None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____5915,
                         false) in
                     Clos uu____5905 in
                   uu____5904 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____5939 =
                    let uu____5942 =
                      let uu____5943 =
                        let uu____5944 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____5944
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____5943] in
                    FStar_Syntax_Subst.open_term uu____5942 body in
                  match uu____5939 with
                  | (bs,body1) ->
                      let lb1 =
                        let uu___171_5950 = lb in
                        let uu____5951 =
                          let uu____5954 =
                            let uu____5955 = FStar_List.hd bs in
                            FStar_All.pipe_right uu____5955 Prims.fst in
                          FStar_All.pipe_right uu____5954
                            (fun _0_32  -> FStar_Util.Inl _0_32) in
                        let uu____5964 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____5967 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = uu____5951;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___171_5950.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____5964;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___171_5950.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5967
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____5977  -> Dummy :: env1)
                             env) in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____5993 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____5993
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____6006 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____6028  ->
                        match uu____6028 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____6067 =
                                let uu___172_6068 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___172_6068.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___172_6068.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____6067 in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos in
                            let memo = FStar_Util.mk_ref None in
                            let rec_env1 = (Clos (env, fix_f_i, memo, true))
                              :: rec_env in
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1")))) (Prims.snd lbs)
                   (env, [], (Prims.parse_int "0")) in
               (match uu____6006 with
                | (rec_env,memos,uu____6128) ->
                    let uu____6143 =
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
                             let uu____6185 =
                               let uu____6186 =
                                 let uu____6196 = FStar_Util.mk_ref None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____6196, false) in
                               Clos uu____6186 in
                             uu____6185 :: env1) (Prims.snd lbs) env in
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
                             FStar_Syntax_Syntax.tk = uu____6234;
                             FStar_Syntax_Syntax.pos = uu____6235;
                             FStar_Syntax_Syntax.vars = uu____6236;_},uu____6237,uu____6238))::uu____6239
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____6245 -> false in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____6252 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____6252
                        then
                          let uu___173_6253 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___173_6253.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps = (uu___173_6253.primitive_steps)
                          }
                        else
                          (let uu___174_6255 = cfg in
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___174_6255.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta];
                             primitive_steps =
                               (uu___174_6255.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____6257 =
                         let uu____6258 = FStar_Syntax_Subst.compress head1 in
                         uu____6258.FStar_Syntax_Syntax.n in
                       match uu____6257 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____6272 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____6272 with
                            | (uu____6273,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____6277 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____6284 =
                                         let uu____6285 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____6285.FStar_Syntax_Syntax.n in
                                       match uu____6284 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____6290,uu____6291))
                                           ->
                                           let uu____6300 =
                                             let uu____6301 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____6301.FStar_Syntax_Syntax.n in
                                           (match uu____6300 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____6306,msrc,uu____6308))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____6317 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                Some uu____6317
                                            | uu____6318 -> None)
                                       | uu____6319 -> None in
                                     let uu____6320 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____6320 with
                                      | Some e ->
                                          let lb1 =
                                            let uu___175_6324 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___175_6324.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___175_6324.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___175_6324.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Syntax_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____6325 =
                                            FStar_List.tl stack1 in
                                          let uu____6326 =
                                            let uu____6327 =
                                              let uu____6330 =
                                                let uu____6331 =
                                                  let uu____6339 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____6339) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____6331 in
                                              FStar_Syntax_Syntax.mk
                                                uu____6330 in
                                            uu____6327 None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____6325 uu____6326
                                      | None  ->
                                          let uu____6356 =
                                            let uu____6357 = is_return body in
                                            match uu____6357 with
                                            | Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____6360;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____6361;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____6362;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____6367 -> false in
                                          if uu____6356
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
                                               let uu____6387 =
                                                 let uu____6390 =
                                                   let uu____6391 =
                                                     let uu____6406 =
                                                       let uu____6408 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____6408] in
                                                     (uu____6406, body1,
                                                       (Some
                                                          (FStar_Util.Inr
                                                             (m1, [])))) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____6391 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____6390 in
                                               uu____6387 None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____6441 =
                                                 let uu____6442 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____6442.FStar_Syntax_Syntax.n in
                                               match uu____6441 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____6448::uu____6449::[])
                                                   ->
                                                   let uu____6455 =
                                                     let uu____6458 =
                                                       let uu____6459 =
                                                         let uu____6464 =
                                                           let uu____6466 =
                                                             let uu____6467 =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____6467 in
                                                           let uu____6468 =
                                                             let uu____6470 =
                                                               let uu____6471
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____6471 in
                                                             [uu____6470] in
                                                           uu____6466 ::
                                                             uu____6468 in
                                                         (bind1, uu____6464) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____6459 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____6458 in
                                                   uu____6455 None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____6483 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____6489 =
                                                 let uu____6492 =
                                                   let uu____6493 =
                                                     let uu____6503 =
                                                       let uu____6505 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____6506 =
                                                         let uu____6508 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____6509 =
                                                           let uu____6511 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____6512 =
                                                             let uu____6514 =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____6515 =
                                                               let uu____6517
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____6518
                                                                 =
                                                                 let uu____6520
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____6520] in
                                                               uu____6517 ::
                                                                 uu____6518 in
                                                             uu____6514 ::
                                                               uu____6515 in
                                                           uu____6511 ::
                                                             uu____6512 in
                                                         uu____6508 ::
                                                           uu____6509 in
                                                       uu____6505 ::
                                                         uu____6506 in
                                                     (bind_inst, uu____6503) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____6493 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____6492 in
                                               uu____6489 None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____6532 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____6532 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____6550 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____6550 with
                            | (uu____6551,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____6574 =
                                        let uu____6575 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____6575.FStar_Syntax_Syntax.n in
                                      match uu____6574 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____6581) -> t4
                                      | uu____6586 -> head2 in
                                    let uu____6587 =
                                      let uu____6588 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____6588.FStar_Syntax_Syntax.n in
                                    match uu____6587 with
                                    | FStar_Syntax_Syntax.Tm_fvar x -> Some x
                                    | uu____6593 -> None in
                                  let uu____6594 = maybe_extract_fv head2 in
                                  match uu____6594 with
                                  | Some x when
                                      let uu____6600 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____6600
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____6604 =
                                          maybe_extract_fv head3 in
                                        match uu____6604 with
                                        | Some uu____6607 -> Some true
                                        | uu____6608 -> Some false in
                                      (head3, action_unfolded)
                                  | uu____6611 -> (head2, None) in
                                ((let is_arg_impure uu____6622 =
                                    match uu____6622 with
                                    | (e,q) ->
                                        let uu____6627 =
                                          let uu____6628 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____6628.FStar_Syntax_Syntax.n in
                                        (match uu____6627 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____6643 -> false) in
                                  let uu____6644 =
                                    let uu____6645 =
                                      let uu____6649 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____6649 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____6645 in
                                  if uu____6644
                                  then
                                    let uu____6652 =
                                      let uu____6653 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____6653 in
                                    failwith uu____6652
                                  else ());
                                 (let uu____6655 =
                                    maybe_unfold_action head_app in
                                  match uu____6655 with
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
                                      let uu____6690 = FStar_List.tl stack1 in
                                      norm cfg env uu____6690 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____6704 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____6704 in
                           let uu____6705 = FStar_List.tl stack1 in
                           norm cfg env uu____6705 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____6788  ->
                                     match uu____6788 with
                                     | (pat,wopt,tm) ->
                                         let uu____6826 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____6826))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____6852 = FStar_List.tl stack1 in
                           norm cfg env uu____6852 tm
                       | uu____6853 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.tk = uu____6862;
                             FStar_Syntax_Syntax.pos = uu____6863;
                             FStar_Syntax_Syntax.vars = uu____6864;_},uu____6865,uu____6866))::uu____6867
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____6873 -> false in
                    if should_reify
                    then
                      let uu____6874 = FStar_List.tl stack1 in
                      let uu____6875 =
                        let uu____6876 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____6876 in
                      norm cfg env uu____6874 uu____6875
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
                           let uu___176_6884 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___176_6884.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___176_6884.primitive_steps)
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
              let uu____6940 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____6940 with
              | (uu____6941,return_repr) ->
                  let return_inst =
                    let uu____6948 =
                      let uu____6949 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____6949.FStar_Syntax_Syntax.n in
                    match uu____6948 with
                    | FStar_Syntax_Syntax.Tm_uinst (return_tm,uu____6955::[])
                        ->
                        let uu____6961 =
                          let uu____6964 =
                            let uu____6965 =
                              let uu____6970 =
                                let uu____6972 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____6972] in
                              (return_tm, uu____6970) in
                            FStar_Syntax_Syntax.Tm_uinst uu____6965 in
                          FStar_Syntax_Syntax.mk uu____6964 in
                        uu____6961 None e.FStar_Syntax_Syntax.pos
                    | uu____6984 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____6987 =
                    let uu____6990 =
                      let uu____6991 =
                        let uu____7001 =
                          let uu____7003 = FStar_Syntax_Syntax.as_arg t in
                          let uu____7004 =
                            let uu____7006 = FStar_Syntax_Syntax.as_arg e in
                            [uu____7006] in
                          uu____7003 :: uu____7004 in
                        (return_inst, uu____7001) in
                      FStar_Syntax_Syntax.Tm_app uu____6991 in
                    FStar_Syntax_Syntax.mk uu____6990 in
                  uu____6987 None e.FStar_Syntax_Syntax.pos
            else
              (let uu____7019 = FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____7019 with
               | None  ->
                   let uu____7021 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____7021
               | Some
                   { FStar_TypeChecker_Env.msource = uu____7022;
                     FStar_TypeChecker_Env.mtarget = uu____7023;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____7024;
                         FStar_TypeChecker_Env.mlift_term = None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | Some
                   { FStar_TypeChecker_Env.msource = uu____7035;
                     FStar_TypeChecker_Env.mtarget = uu____7036;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____7037;
                         FStar_TypeChecker_Env.mlift_term = Some lift;_};_}
                   ->
                   let uu____7055 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____7055)
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
                (fun uu____7085  ->
                   match uu____7085 with
                   | (a,imp) ->
                       let uu____7092 = norm cfg env [] a in
                       (uu____7092, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___177_7107 = comp1 in
            let uu____7110 =
              let uu____7111 =
                let uu____7117 = norm cfg env [] t in
                let uu____7118 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____7117, uu____7118) in
              FStar_Syntax_Syntax.Total uu____7111 in
            {
              FStar_Syntax_Syntax.n = uu____7110;
              FStar_Syntax_Syntax.tk = (uu___177_7107.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___177_7107.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___177_7107.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___178_7133 = comp1 in
            let uu____7136 =
              let uu____7137 =
                let uu____7143 = norm cfg env [] t in
                let uu____7144 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____7143, uu____7144) in
              FStar_Syntax_Syntax.GTotal uu____7137 in
            {
              FStar_Syntax_Syntax.n = uu____7136;
              FStar_Syntax_Syntax.tk = (uu___178_7133.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___178_7133.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___178_7133.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____7175  ->
                      match uu____7175 with
                      | (a,i) ->
                          let uu____7182 = norm cfg env [] a in
                          (uu____7182, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___141_7187  ->
                      match uu___141_7187 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____7191 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____7191
                      | f -> f)) in
            let uu___179_7195 = comp1 in
            let uu____7198 =
              let uu____7199 =
                let uu___180_7200 = ct in
                let uu____7201 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____7202 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____7205 = norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____7201;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___180_7200.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____7202;
                  FStar_Syntax_Syntax.effect_args = uu____7205;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____7199 in
            {
              FStar_Syntax_Syntax.n = uu____7198;
              FStar_Syntax_Syntax.tk = (uu___179_7195.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___179_7195.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___179_7195.FStar_Syntax_Syntax.vars)
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
            (let uu___181_7222 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___181_7222.tcenv);
               delta_level = (uu___181_7222.delta_level);
               primitive_steps = (uu___181_7222.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____7227 = norm1 t in
          FStar_Syntax_Util.non_informative uu____7227 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____7230 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___182_7244 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.tk = (uu___182_7244.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___182_7244.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___182_7244.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____7254 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____7254
            then
              let ct1 =
                match downgrade_ghost_effect_name
                        ct.FStar_Syntax_Syntax.effect_name
                with
                | Some pure_eff ->
                    let uu___183_7259 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___183_7259.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___183_7259.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___183_7259.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___183_7259.FStar_Syntax_Syntax.flags)
                    }
                | None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___184_7261 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___184_7261.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Syntax_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___184_7261.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___184_7261.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___184_7261.FStar_Syntax_Syntax.flags)
                    } in
              let uu___185_7262 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.tk =
                  (uu___185_7262.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___185_7262.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___185_7262.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____7268 -> c
and norm_binder:
  cfg ->
    env ->
      FStar_Syntax_Syntax.binder ->
        (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  =
  fun cfg  ->
    fun env  ->
      fun uu____7271  ->
        match uu____7271 with
        | (x,imp) ->
            let uu____7274 =
              let uu___186_7275 = x in
              let uu____7276 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___186_7275.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___186_7275.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____7276
              } in
            (uu____7274, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____7282 =
          FStar_List.fold_left
            (fun uu____7289  ->
               fun b  ->
                 match uu____7289 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____7282 with | (nbs,uu____7306) -> FStar_List.rev nbs
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
            let uu____7323 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
            if uu____7323
            then
              let t = norm cfg env [] lc.FStar_Syntax_Syntax.res_typ in
              let uu____7328 = FStar_Syntax_Util.is_total_lcomp lc in
              (if uu____7328
               then
                 let uu____7332 =
                   let uu____7335 =
                     let uu____7336 =
                       let uu____7339 = FStar_Syntax_Syntax.mk_Total t in
                       FStar_Syntax_Util.comp_set_flags uu____7339 flags in
                     FStar_Syntax_Util.lcomp_of_comp uu____7336 in
                   FStar_Util.Inl uu____7335 in
                 Some uu____7332
               else
                 (let uu____7343 =
                    let uu____7346 =
                      let uu____7347 =
                        let uu____7350 = FStar_Syntax_Syntax.mk_GTotal t in
                        FStar_Syntax_Util.comp_set_flags uu____7350 flags in
                      FStar_Syntax_Util.lcomp_of_comp uu____7347 in
                    FStar_Util.Inl uu____7346 in
                  Some uu____7343))
            else
              Some
                (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags))
        | uu____7363 -> lopt
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
              ((let uu____7375 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____7375
                then
                  let uu____7376 = FStar_Syntax_Print.term_to_string tm in
                  let uu____7377 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2 "Normalized %s to %s\n" uu____7376
                    uu____7377
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___187_7388 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___187_7388.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____7408  ->
                    let uu____7409 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____7409);
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
              let uu____7446 =
                let uu___188_7447 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___188_7447.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___188_7447.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___188_7447.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____7446
          | (Arg (Univ _,_,_))::_|(Arg (Dummy ,_,_))::_ ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____7469),aq,r))::stack2 ->
              (log cfg
                 (fun uu____7485  ->
                    let uu____7486 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____7486);
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
                 (let uu____7497 = FStar_ST.read m in
                  match uu____7497 with
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
                  | Some (uu____7523,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq) None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.extend_app head1 (t, aq) None r in
              let uu____7545 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____7545
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____7552  ->
                    let uu____7553 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____7553);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____7558 =
                  log cfg
                    (fun uu____7560  ->
                       let uu____7561 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____7562 =
                         let uu____7563 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____7570  ->
                                   match uu____7570 with
                                   | (p,uu____7576,uu____7577) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____7563
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____7561 uu____7562);
                  (let whnf = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___142_7587  ->
                               match uu___142_7587 with
                               | FStar_TypeChecker_Env.Inlining 
                                 |FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____7588 -> false)) in
                     let steps' =
                       let uu____7591 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____7591
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___189_7594 = cfg in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___189_7594.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___189_7594.primitive_steps)
                     } in
                   let norm_or_whnf env2 t1 =
                     if whnf
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____7628 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_disj [] ->
                         failwith "Impossible"
                     | FStar_Syntax_Syntax.Pat_disj (hd1::tl1) ->
                         let uu____7648 = norm_pat env2 hd1 in
                         (match uu____7648 with
                          | (hd2,env') ->
                              let tl2 =
                                FStar_All.pipe_right tl1
                                  (FStar_List.map
                                     (fun p1  ->
                                        let uu____7684 = norm_pat env2 p1 in
                                        Prims.fst uu____7684)) in
                              ((let uu___190_7696 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_disj (hd2 ::
                                       tl2));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___190_7696.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___190_7696.FStar_Syntax_Syntax.p)
                                }), env'))
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____7713 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____7747  ->
                                   fun uu____7748  ->
                                     match (uu____7747, uu____7748) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____7813 = norm_pat env3 p1 in
                                         (match uu____7813 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____7713 with
                          | (pats1,env3) ->
                              ((let uu___191_7879 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___191_7879.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___191_7879.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___192_7893 = x in
                           let uu____7894 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___192_7893.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___192_7893.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____7894
                           } in
                         ((let uu___193_7900 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___193_7900.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___193_7900.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___194_7905 = x in
                           let uu____7906 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___194_7905.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___194_7905.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____7906
                           } in
                         ((let uu___195_7912 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___195_7912.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___195_7912.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___196_7922 = x in
                           let uu____7923 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___196_7922.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___196_7922.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____7923
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___197_7930 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.ty =
                               (uu___197_7930.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___197_7930.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf -> branches
                     | uu____7934 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____7937 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____7937 with
                                 | (p,wopt,e) ->
                                     let uu____7955 = norm_pat env1 p in
                                     (match uu____7955 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | None  -> None
                                            | Some w ->
                                                let uu____7979 =
                                                  norm_or_whnf env2 w in
                                                Some uu____7979 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____7984 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____7984) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____7994) -> is_cons h
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
                  | uu____8005 -> false in
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
                  let uu____8104 = FStar_Syntax_Util.head_and_args scrutinee2 in
                  match uu____8104 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_disj ps ->
                           let mopt =
                             FStar_Util.find_map ps
                               (fun p1  ->
                                  let m = matches_pat scrutinee2 p1 in
                                  match m with
                                  | FStar_Util.Inl uu____8161 -> Some m
                                  | FStar_Util.Inr (true ) -> Some m
                                  | FStar_Util.Inr (false ) -> None) in
                           (match mopt with
                            | None  -> FStar_Util.Inr false
                            | Some m -> m)
                       | FStar_Syntax_Syntax.Pat_var _
                         |FStar_Syntax_Syntax.Pat_wild _ ->
                           FStar_Util.Inl [scrutinee2]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____8192 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____8204 ->
                                let uu____8205 =
                                  let uu____8206 = is_cons head1 in
                                  Prims.op_Negation uu____8206 in
                                FStar_Util.Inr uu____8205)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____8220 =
                             let uu____8221 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____8221.FStar_Syntax_Syntax.n in
                           (match uu____8220 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____8228 ->
                                let uu____8229 =
                                  let uu____8230 = is_cons head1 in
                                  Prims.op_Negation uu____8230 in
                                FStar_Util.Inr uu____8229))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____8264)::rest_a,(p1,uu____8267)::rest_p) ->
                      let uu____8295 = matches_pat t1 p1 in
                      (match uu____8295 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____8309 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____8380 = matches_pat scrutinee1 p1 in
                      (match uu____8380 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____8390  ->
                                 let uu____8391 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____8392 =
                                   let uu____8393 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____8393
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____8391 uu____8392);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____8402 =
                                        let uu____8403 =
                                          let uu____8413 =
                                            FStar_Util.mk_ref (Some ([], t1)) in
                                          ([], t1, uu____8413, false) in
                                        Clos uu____8403 in
                                      uu____8402 :: env2) env1 s in
                             let uu____8436 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____8436))) in
                let uu____8437 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____8437
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___143_8451  ->
                match uu___143_8451 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | uu____8454 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____8458 -> d in
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
            let uu___198_8478 = config s e in
            {
              steps = (uu___198_8478.steps);
              tcenv = (uu___198_8478.tcenv);
              delta_level = (uu___198_8478.delta_level);
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
      fun t  -> let uu____8497 = config s e in norm_comp uu____8497 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  -> let uu____8504 = config [] env in norm_universe uu____8504 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun c  ->
      let uu____8511 = config [] env in ghost_to_pure_aux uu____8511 [] c
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
        let uu____8523 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____8523 in
      let uu____8524 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____8524
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | Some pure_eff ->
            let uu___199_8526 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___199_8526.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___199_8526.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____8527  ->
                    let uu____8528 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____8528))
            }
        | None  -> lc
      else lc
let term_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun env  ->
    fun t  ->
      let uu____8536 = normalize [AllowUnboundUniverses] env t in
      FStar_Syntax_Print.term_to_string uu____8536
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let uu____8543 =
        let uu____8544 = config [AllowUnboundUniverses] env in
        norm_comp uu____8544 [] c in
      FStar_Syntax_Print.comp_to_string uu____8543
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
                   let uu____8581 =
                     let uu____8582 =
                       let uu____8587 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____8587) in
                     FStar_Syntax_Syntax.Tm_refine uu____8582 in
                   mk uu____8581 t01.FStar_Syntax_Syntax.pos
               | uu____8592 -> t2)
          | uu____8593 -> t2 in
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
        let uu____8609 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____8609 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____8625 ->
                 let uu____8629 = FStar_Syntax_Util.abs_formals e in
                 (match uu____8629 with
                  | (actuals,uu____8640,uu____8641) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____8663 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____8663 with
                         | (binders,args) ->
                             let uu____8673 =
                               (FStar_Syntax_Syntax.mk_Tm_app e args) None
                                 e.FStar_Syntax_Syntax.pos in
                             let uu____8678 =
                               let uu____8685 =
                                 FStar_All.pipe_right
                                   (FStar_Syntax_Util.lcomp_of_comp c)
                                   (fun _0_33  -> FStar_Util.Inl _0_33) in
                               FStar_All.pipe_right uu____8685
                                 (fun _0_34  -> Some _0_34) in
                             FStar_Syntax_Util.abs binders uu____8673
                               uu____8678)))
let eta_expand:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____8721 =
        let uu____8725 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
        (uu____8725, (t.FStar_Syntax_Syntax.n)) in
      match uu____8721 with
      | (Some sort,uu____8732) ->
          let uu____8734 = mk sort t.FStar_Syntax_Syntax.pos in
          eta_expand_with_type env t uu____8734
      | (uu____8735,FStar_Syntax_Syntax.Tm_name x) ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____8739 ->
          let uu____8743 = FStar_Syntax_Util.head_and_args t in
          (match uu____8743 with
           | (head1,args) ->
               let uu____8769 =
                 let uu____8770 = FStar_Syntax_Subst.compress head1 in
                 uu____8770.FStar_Syntax_Syntax.n in
               (match uu____8769 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____8773,thead) ->
                    let uu____8787 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____8787 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____8818 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___200_8822 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___200_8822.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___200_8822.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___200_8822.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___200_8822.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___200_8822.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___200_8822.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ = None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___200_8822.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___200_8822.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___200_8822.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___200_8822.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___200_8822.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___200_8822.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___200_8822.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___200_8822.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___200_8822.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___200_8822.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___200_8822.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___200_8822.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___200_8822.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___200_8822.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___200_8822.FStar_TypeChecker_Env.qname_and_index)
                                 }) t in
                            match uu____8818 with
                            | (uu____8823,ty,uu____8825) ->
                                eta_expand_with_type env t ty))
                | uu____8826 ->
                    let uu____8827 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___201_8831 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___201_8831.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___201_8831.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___201_8831.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___201_8831.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___201_8831.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___201_8831.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ = None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___201_8831.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___201_8831.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___201_8831.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___201_8831.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___201_8831.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___201_8831.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___201_8831.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___201_8831.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___201_8831.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___201_8831.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___201_8831.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___201_8831.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___201_8831.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___201_8831.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___201_8831.FStar_TypeChecker_Env.qname_and_index)
                         }) t in
                    (match uu____8827 with
                     | (uu____8832,ty,uu____8834) ->
                         eta_expand_with_type env t ty)))