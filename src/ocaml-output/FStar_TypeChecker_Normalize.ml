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
  let arg_as_bounded_int uu____2512 =
    match uu____2512 with
    | (a,uu____2519) ->
        let uu____2523 =
          let uu____2524 = FStar_Syntax_Subst.compress a in
          uu____2524.FStar_Syntax_Syntax.n in
        (match uu____2523 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.tk = uu____2531;
                FStar_Syntax_Syntax.pos = uu____2532;
                FStar_Syntax_Syntax.vars = uu____2533;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,None ));
                                                            FStar_Syntax_Syntax.tk
                                                              = uu____2535;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____2536;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____2537;_},uu____2538)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____2569 =
               let uu____2572 = FStar_Util.int_of_string i in
               (fv1, uu____2572) in
             Some uu____2569
         | uu____2575 -> None) in
  let arg_as_bool uu____2584 =
    match uu____2584 with
    | (a,uu____2589) ->
        let uu____2591 =
          let uu____2592 = FStar_Syntax_Subst.compress a in
          uu____2592.FStar_Syntax_Syntax.n in
        (match uu____2591 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
             Some b
         | uu____2597 -> None) in
  let arg_as_char uu____2604 =
    match uu____2604 with
    | (a,uu____2609) ->
        let uu____2611 =
          let uu____2612 = FStar_Syntax_Subst.compress a in
          uu____2612.FStar_Syntax_Syntax.n in
        (match uu____2611 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
             Some c
         | uu____2617 -> None) in
  let arg_as_string uu____2624 =
    match uu____2624 with
    | (a,uu____2629) ->
        let uu____2631 =
          let uu____2632 = FStar_Syntax_Subst.compress a in
          uu____2632.FStar_Syntax_Syntax.n in
        (match uu____2631 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (bytes,uu____2637)) -> Some (FStar_Util.string_of_bytes bytes)
         | uu____2640 -> None) in
  let arg_as_list f uu____2661 =
    match uu____2661 with
    | (a,uu____2670) ->
        let rec sequence l =
          match l with
          | [] -> Some []
          | (None )::uu____2689 -> None
          | (Some x)::xs ->
              let uu____2699 = sequence xs in
              (match uu____2699 with
               | None  -> None
               | Some xs' -> Some (x :: xs')) in
        let uu____2710 = FStar_Syntax_Util.list_elements a in
        (match uu____2710 with
         | None  -> None
         | Some elts ->
             let uu____2720 =
               FStar_List.map
                 (fun x  ->
                    let uu____2725 = FStar_Syntax_Syntax.as_arg x in
                    f uu____2725) elts in
             sequence uu____2720) in
  let lift_unary f aopts =
    match aopts with
    | (Some a)::[] -> let uu____2755 = f a in Some uu____2755
    | uu____2756 -> None in
  let lift_binary f aopts =
    match aopts with
    | (Some a0)::(Some a1)::[] -> let uu____2795 = f a0 a1 in Some uu____2795
    | uu____2796 -> None in
  let unary_op as_a f r args =
    let uu____2840 = FStar_List.map as_a args in lift_unary (f r) uu____2840 in
  let binary_op as_a f r args =
    let uu____2890 = FStar_List.map as_a args in lift_binary (f r) uu____2890 in
  let as_primitive_step uu____2907 =
    match uu____2907 with
    | (l,arity,f) ->
        { name = l; arity; strong_reduction_ok = true; interpretation = f } in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  -> fun x  -> let uu____2945 = f x in int_as_const r uu____2945) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2968 = f x y in int_as_const r uu____2968) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  -> fun x  -> let uu____2985 = f x in bool_as_const r uu____2985) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  -> let uu____3008 = f x y in bool_as_const r uu____3008) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  -> let uu____3031 = f x y in string_as_const r uu____3031) in
  let list_of_string' rng s =
    let name l =
      let uu____3045 =
        let uu____3046 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            None in
        FStar_Syntax_Syntax.Tm_fvar uu____3046 in
      mk uu____3045 rng in
    let char_t = name FStar_Syntax_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____3056 =
      let uu____3058 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____3058 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____3056 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Const.exp_string s in
  let string_of_int1 rng i =
    let uu____3080 = FStar_Util.string_of_int i in
    string_as_const rng uu____3080 in
  let string_of_bool1 rng b =
    string_as_const rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____3096 = FStar_Util.string_of_int i in
    string_as_const rng uu____3096 in
  let string_of_bool2 rng b =
    string_as_const rng (if b then "true" else "false") in
  let basic_ops =
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
                                      let uu____3284 =
                                        FStar_Syntax_Const.p2l
                                          ["FStar";
                                          "String";
                                          "list_of_string"] in
                                      (uu____3284, (Prims.parse_int "1"),
                                        (unary_op arg_as_string
                                           list_of_string')) in
                                    let uu____3290 =
                                      let uu____3300 =
                                        let uu____3309 =
                                          FStar_Syntax_Const.p2l
                                            ["FStar";
                                            "String";
                                            "string_of_list"] in
                                        (uu____3309, (Prims.parse_int "1"),
                                          (unary_op (arg_as_list arg_as_char)
                                             string_of_list')) in
                                      [uu____3300] in
                                    uu____3275 :: uu____3290 in
                                  (FStar_Syntax_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_bool string_of_bool2))
                                    :: uu____3265 in
                                (FStar_Syntax_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (unary_op arg_as_int string_of_int2)) ::
                                  uu____3255 in
                              (FStar_Syntax_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____3245 in
                            (FStar_Syntax_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____3235 in
                          (FStar_Syntax_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____3225 in
                        (FStar_Syntax_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____3215 in
                      (FStar_Syntax_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____3205 in
                    (FStar_Syntax_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
                      :: uu____3195 in
                  (FStar_Syntax_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____3185 in
                (FStar_Syntax_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____3175 in
              (FStar_Syntax_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____3165 in
            (FStar_Syntax_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____3155 in
          (FStar_Syntax_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____3145 in
        (FStar_Syntax_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____3135 in
      (FStar_Syntax_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____3125 in
    (FStar_Syntax_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____3115 in
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
      let uu____3604 =
        let uu____3605 =
          let uu____3606 = FStar_Syntax_Syntax.as_arg c in [uu____3606] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____3605 in
      uu____3604 None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____3630 =
              let uu____3639 = FStar_Syntax_Const.p2l ["FStar"; m; "add"] in
              (uu____3639, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____3648  ->
                        fun uu____3649  ->
                          match (uu____3648, uu____3649) with
                          | ((int_to_t1,x),(uu____3660,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____3666 =
              let uu____3676 =
                let uu____3685 = FStar_Syntax_Const.p2l ["FStar"; m; "sub"] in
                (uu____3685, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____3694  ->
                          fun uu____3695  ->
                            match (uu____3694, uu____3695) with
                            | ((int_to_t1,x),(uu____3706,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____3712 =
                let uu____3722 =
                  let uu____3731 = FStar_Syntax_Const.p2l ["FStar"; m; "mul"] in
                  (uu____3731, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____3740  ->
                            fun uu____3741  ->
                              match (uu____3740, uu____3741) with
                              | ((int_to_t1,x),(uu____3752,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____3722] in
              uu____3676 :: uu____3712 in
            uu____3630 :: uu____3666)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_bool rng args =
    match args with
    | (_typ,uu____3818)::(a1,uu____3820)::(a2,uu____3822)::[] ->
        let uu____3851 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3851 with
         | FStar_Syntax_Util.Equal  ->
             let uu____3853 =
               mk
                 (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_bool true)) rng in
             Some uu____3853
         | FStar_Syntax_Util.NotEqual  ->
             let uu____3858 =
               mk
                 (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_bool false)) rng in
             Some uu____3858
         | uu____3863 -> None)
    | uu____3864 -> failwith "Unexpected number of arguments" in
  let interp_prop r args =
    match args with
    | (_typ,_)::(a1,_)::(a2,_)::[]|(_typ,_)::_::(a1,_)::(a2,_)::[] ->
        let uu____3946 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3946 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___160_3950 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___160_3950.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___160_3950.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___160_3950.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___161_3957 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___161_3957.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___161_3957.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___161_3957.FStar_Syntax_Syntax.vars)
                })
         | uu____3962 -> None)
    | uu____3963 -> failwith "Unexpected number of arguments" in
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
      let uu____3974 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops cfg.steps) in
      if uu____3974
      then tm
      else
        (let uu____3976 = FStar_Syntax_Util.head_and_args tm in
         match uu____3976 with
         | (head1,args) ->
             let uu____4002 =
               let uu____4003 = FStar_Syntax_Util.un_uinst head1 in
               uu____4003.FStar_Syntax_Syntax.n in
             (match uu____4002 with
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____4007 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps in
                  (match uu____4007 with
                   | None  -> tm
                   | Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then tm
                       else
                         (let uu____4019 =
                            prim_step.interpretation
                              head1.FStar_Syntax_Syntax.pos args in
                          match uu____4019 with
                          | None  -> tm
                          | Some reduced -> reduced))
              | uu____4022 -> tm))
let reduce_equality:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___162_4029 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___162_4029.tcenv);
           delta_level = (uu___162_4029.delta_level);
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
        let uu___163_4051 = t in
        {
          FStar_Syntax_Syntax.n = (uu___163_4051.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___163_4051.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___163_4051.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid ->
            Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid ->
            Some false
        | uu____4070 -> None in
      let simplify arg = ((simp_t (Prims.fst arg)), arg) in
      let uu____4097 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps) in
      if uu____4097
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
             let uu____4137 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____4137
             then
               let uu____4138 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____4138 with
                | (Some (true ),_)::(_,(arg,_))::[]
                  |(_,(arg,_))::(Some (true ),_)::[] -> arg
                | (Some (false ),_)::_::[]|_::(Some (false ),_)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4304 -> tm)
             else
               (let uu____4314 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____4314
                then
                  let uu____4315 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____4315 with
                  | (Some (true ),_)::_::[]|_::(Some (true ),_)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),_)::(_,(arg,_))::[]
                    |(_,(arg,_))::(Some (false ),_)::[] -> arg
                  | uu____4481 -> tm
                else
                  (let uu____4491 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____4491
                   then
                     let uu____4492 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____4492 with
                     | _::(Some (true ),_)::[]|(Some (false ),_)::_::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____4581)::(uu____4582,(arg,uu____4584))::[]
                         -> arg
                     | uu____4625 -> tm
                   else
                     (let uu____4635 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____4635
                      then
                        let uu____4636 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____4636 with
                        | (Some (true ),uu____4669)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____4693)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____4717 -> tm
                      else
                        (let uu____4727 =
                           (FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Syntax_Const.forall_lid)
                             ||
                             (FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid) in
                         if uu____4727
                         then
                           match args with
                           | (t,_)::[]
                             |(_,Some (FStar_Syntax_Syntax.Implicit _))::
                             (t,_)::[] ->
                               let uu____4768 =
                                 let uu____4769 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____4769.FStar_Syntax_Syntax.n in
                               (match uu____4768 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____4772::[],body,uu____4774) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | Some (false ) ->
                                         w FStar_Syntax_Util.t_false
                                     | uu____4800 -> tm)
                                | uu____4802 -> tm)
                           | uu____4803 -> tm
                         else reduce_equality cfg tm))))
         | uu____4810 -> tm)
let is_norm_request hd1 args =
  let uu____4825 =
    let uu____4829 =
      let uu____4830 = FStar_Syntax_Util.un_uinst hd1 in
      uu____4830.FStar_Syntax_Syntax.n in
    (uu____4829, args) in
  match uu____4825 with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4835::uu____4836::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize_term
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4839::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize
  | uu____4841 -> false
let get_norm_request args =
  match args with
  | _::(tm,_)::[]|(tm,_)::[] -> tm
  | uu____4874 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___138_4881  ->
    match uu___138_4881 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.tk = uu____4883;
           FStar_Syntax_Syntax.pos = uu____4884;
           FStar_Syntax_Syntax.vars = uu____4885;_},uu____4886,uu____4887))::uu____4888
        -> true
    | uu____4894 -> false
let is_fstar_tactics_embed: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____4899 =
      let uu____4900 = FStar_Syntax_Util.un_uinst t in
      uu____4900.FStar_Syntax_Syntax.n in
    match uu____4899 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Syntax_Const.fstar_tactics_embed_lid
    | uu____4904 -> false
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
            (fun uu____5018  ->
               let uu____5019 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____5020 = FStar_Syntax_Print.term_to_string t1 in
               let uu____5021 =
                 let uu____5022 =
                   let uu____5024 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left Prims.fst uu____5024 in
                 stack_to_string uu____5022 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____5019
                 uu____5020 uu____5021);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____5036 ->
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
                  FStar_Syntax_Syntax.tk = uu____5068;
                  FStar_Syntax_Syntax.pos = uu____5069;
                  FStar_Syntax_Syntax.vars = uu____5070;_},uu____5071)
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Syntax_Const.fstar_tactics_embed_lid
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               is_fstar_tactics_embed hd1 ->
               let args1 = closures_as_args_delayed cfg env args in
               let t2 =
                 let uu___164_5111 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd1, args1));
                   FStar_Syntax_Syntax.tk =
                     (uu___164_5111.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___164_5111.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___164_5111.FStar_Syntax_Syntax.vars)
                 } in
               let t3 = reduce_primops cfg t2 in rebuild cfg env stack1 t3
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____5140 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____5140) && (is_norm_request hd1 args))
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
                 let uu___165_5153 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___165_5153.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___165_5153.primitive_steps)
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
                  FStar_Syntax_Syntax.tk = uu____5158;
                  FStar_Syntax_Syntax.pos = uu____5159;
                  FStar_Syntax_Syntax.vars = uu____5160;_},a1::a2::rest)
               ->
               let uu____5194 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____5194 with
                | (hd1,uu____5205) ->
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
                    (FStar_Const.Const_reflect uu____5260);
                  FStar_Syntax_Syntax.tk = uu____5261;
                  FStar_Syntax_Syntax.pos = uu____5262;
                  FStar_Syntax_Syntax.vars = uu____5263;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____5286 = FStar_List.tl stack1 in
               norm cfg env uu____5286 (Prims.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.tk = uu____5289;
                  FStar_Syntax_Syntax.pos = uu____5290;
                  FStar_Syntax_Syntax.vars = uu____5291;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____5314 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____5314 with
                | (reify_head,uu____5325) ->
                    let a1 =
                      let uu____5341 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (Prims.fst a) in
                      FStar_Syntax_Subst.compress uu____5341 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____5344);
                            FStar_Syntax_Syntax.tk = uu____5345;
                            FStar_Syntax_Syntax.pos = uu____5346;
                            FStar_Syntax_Syntax.vars = uu____5347;_},a2::[])
                         -> norm cfg env stack1 (Prims.fst a2)
                     | uu____5372 ->
                         let stack2 =
                           (App
                              (reify_head, None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____5380 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____5380
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____5387 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____5387
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____5390 =
                      let uu____5394 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____5394, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____5390 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___139_5403  ->
                         match uu___139_5403 with
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
                    let uu____5407 = FStar_Syntax_Syntax.range_of_fv f in
                    FStar_TypeChecker_Env.set_range cfg.tcenv uu____5407 in
                  let uu____5408 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  match uu____5408 with
                  | None  ->
                      (log cfg
                         (fun uu____5419  ->
                            FStar_Util.print "Tm_fvar case 2\n" []);
                       rebuild cfg env stack1 t1)
                  | Some (us,t2) ->
                      (log cfg
                         (fun uu____5425  ->
                            let uu____5426 =
                              FStar_Syntax_Print.term_to_string t0 in
                            let uu____5427 =
                              FStar_Syntax_Print.term_to_string t2 in
                            FStar_Util.print2 ">>> Unfolded %s to %s\n"
                              uu____5426 uu____5427);
                       (let n1 = FStar_List.length us in
                        if n1 > (Prims.parse_int "0")
                        then
                          match stack1 with
                          | (UnivArgs (us',uu____5434))::stack2 ->
                              let env1 =
                                FStar_All.pipe_right us'
                                  (FStar_List.fold_left
                                     (fun env1  -> fun u  -> (Univ u) :: env1)
                                     env) in
                              norm cfg env1 stack2 t2
                          | uu____5447 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack1 t2
                          | uu____5448 ->
                              let uu____5449 =
                                let uu____5450 =
                                  FStar_Syntax_Print.lid_to_string
                                    (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                FStar_Util.format1
                                  "Impossible: missing universe instantiation on %s"
                                  uu____5450 in
                              failwith uu____5449
                        else norm cfg env stack1 t2)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____5457 = lookup_bvar env x in
               (match uu____5457 with
                | Univ uu____5458 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____5473 = FStar_ST.read r in
                      (match uu____5473 with
                       | Some (env2,t') ->
                           (log cfg
                              (fun uu____5492  ->
                                 let uu____5493 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____5494 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____5493
                                   uu____5494);
                            (let uu____5495 =
                               let uu____5496 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____5496.FStar_Syntax_Syntax.n in
                             match uu____5495 with
                             | FStar_Syntax_Syntax.Tm_abs uu____5499 ->
                                 norm cfg env2 stack1 t'
                             | uu____5514 -> rebuild cfg env2 stack1 t'))
                       | None  -> norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____5547)::uu____5548 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____5553)::uu____5554 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____5560,uu____5561))::stack_rest ->
                    (match c with
                     | Univ uu____5564 -> norm cfg (c :: env) stack_rest t1
                     | uu____5565 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____5568::[] ->
                              (match lopt with
                               | None  when FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____5581  ->
                                         let uu____5582 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____5582);
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
                                           (fun uu___140_5596  ->
                                              match uu___140_5596 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____5597 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____5599  ->
                                         let uu____5600 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____5600);
                                    norm cfg (c :: env) stack_rest body)
                               | Some (FStar_Util.Inl lc) when
                                   FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                                   ->
                                   (log cfg
                                      (fun uu____5611  ->
                                         let uu____5612 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____5612);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____5613 when
                                   FStar_All.pipe_right cfg.steps
                                     (FStar_List.contains Reify)
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____5620 ->
                                   let cfg1 =
                                     let uu___166_5628 = cfg in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___166_5628.tcenv);
                                       delta_level =
                                         (uu___166_5628.delta_level);
                                       primitive_steps =
                                         (uu___166_5628.primitive_steps)
                                     } in
                                   let uu____5629 =
                                     closure_as_term cfg1 env t1 in
                                   rebuild cfg1 env stack1 uu____5629)
                          | uu____5630::tl1 ->
                              (log cfg
                                 (fun uu____5640  ->
                                    let uu____5641 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____5641);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___167_5665 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___167_5665.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____5678  ->
                          let uu____5679 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____5679);
                     norm cfg env stack2 t1)
                | (Debug _)::_
                  |(Meta _)::_|(Let _)::_|(App _)::_|(Abs _)::_|[] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____5690 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____5690
                    else
                      (let uu____5692 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____5692 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____5721 =
                                   let uu____5727 =
                                     let uu____5728 =
                                       let uu____5729 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____5729 in
                                     FStar_All.pipe_right uu____5728
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____5727
                                     (fun _0_30  -> FStar_Util.Inl _0_30) in
                                 FStar_All.pipe_right uu____5721
                                   (fun _0_31  -> Some _0_31)
                             | uu____5754 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____5768  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____5773  ->
                                 let uu____5774 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____5774);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___168_5784 = cfg in
                               let uu____5785 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___168_5784.steps);
                                 tcenv = (uu___168_5784.tcenv);
                                 delta_level = (uu___168_5784.delta_level);
                                 primitive_steps = uu____5785
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
                      (fun uu____5817  ->
                         fun stack2  ->
                           match uu____5817 with
                           | (a,aq) ->
                               let uu____5825 =
                                 let uu____5826 =
                                   let uu____5830 =
                                     let uu____5831 =
                                       let uu____5841 =
                                         FStar_Util.mk_ref None in
                                       (env, a, uu____5841, false) in
                                     Clos uu____5831 in
                                   (uu____5830, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____5826 in
                               uu____5825 :: stack2) args) in
               (log cfg
                  (fun uu____5863  ->
                     let uu____5864 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____5864);
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
                             ((let uu___169_5885 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___169_5885.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___169_5885.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____5886 ->
                      let uu____5889 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____5889)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____5892 = FStar_Syntax_Subst.open_term [(x, None)] f in
                  match uu____5892 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____5908 =
                          let uu____5909 =
                            let uu____5914 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___170_5915 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___170_5915.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___170_5915.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____5914) in
                          FStar_Syntax_Syntax.Tm_refine uu____5909 in
                        mk uu____5908 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____5928 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____5928
               else
                 (let uu____5930 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____5930 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____5936 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  -> fun uu____5942  -> Dummy :: env1)
                               env) in
                        norm_comp cfg uu____5936 c1 in
                      let t2 =
                        let uu____5949 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____5949 c2 in
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
                | uu____6006 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____6009  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____6022 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____6022
                        | FStar_Util.Inr c ->
                            let uu____6030 = norm_comp cfg env c in
                            FStar_Util.Inr uu____6030 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____6035 =
                        mk
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (t12, (tc1, tacopt1), l))
                          t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____6035)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____6086,{
                              FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                uu____6087;
                              FStar_Syntax_Syntax.lbunivs = uu____6088;
                              FStar_Syntax_Syntax.lbtyp = uu____6089;
                              FStar_Syntax_Syntax.lbeff = uu____6090;
                              FStar_Syntax_Syntax.lbdef = uu____6091;_}::uu____6092),uu____6093)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____6119 =
                 (let uu____6120 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____6120) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____6121 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____6121))) in
               if uu____6119
               then
                 let env1 =
                   let uu____6124 =
                     let uu____6125 =
                       let uu____6135 = FStar_Util.mk_ref None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____6135,
                         false) in
                     Clos uu____6125 in
                   uu____6124 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____6159 =
                    let uu____6162 =
                      let uu____6163 =
                        let uu____6164 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____6164
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____6163] in
                    FStar_Syntax_Subst.open_term uu____6162 body in
                  match uu____6159 with
                  | (bs,body1) ->
                      let lb1 =
                        let uu___171_6170 = lb in
                        let uu____6171 =
                          let uu____6174 =
                            let uu____6175 = FStar_List.hd bs in
                            FStar_All.pipe_right uu____6175 Prims.fst in
                          FStar_All.pipe_right uu____6174
                            (fun _0_32  -> FStar_Util.Inl _0_32) in
                        let uu____6184 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____6187 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = uu____6171;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___171_6170.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____6184;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___171_6170.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____6187
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____6197  -> Dummy :: env1)
                             env) in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____6213 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____6213
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____6226 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____6248  ->
                        match uu____6248 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____6287 =
                                let uu___172_6288 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___172_6288.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___172_6288.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____6287 in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos in
                            let memo = FStar_Util.mk_ref None in
                            let rec_env1 = (Clos (env, fix_f_i, memo, true))
                              :: rec_env in
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1")))) (Prims.snd lbs)
                   (env, [], (Prims.parse_int "0")) in
               (match uu____6226 with
                | (rec_env,memos,uu____6348) ->
                    let uu____6363 =
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
                             let uu____6405 =
                               let uu____6406 =
                                 let uu____6416 = FStar_Util.mk_ref None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____6416, false) in
                               Clos uu____6406 in
                             uu____6405 :: env1) (Prims.snd lbs) env in
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
                             FStar_Syntax_Syntax.tk = uu____6454;
                             FStar_Syntax_Syntax.pos = uu____6455;
                             FStar_Syntax_Syntax.vars = uu____6456;_},uu____6457,uu____6458))::uu____6459
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____6465 -> false in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____6472 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____6472
                        then
                          let uu___173_6473 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___173_6473.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps = (uu___173_6473.primitive_steps)
                          }
                        else
                          (let uu___174_6475 = cfg in
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___174_6475.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta];
                             primitive_steps =
                               (uu___174_6475.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____6477 =
                         let uu____6478 = FStar_Syntax_Subst.compress head1 in
                         uu____6478.FStar_Syntax_Syntax.n in
                       match uu____6477 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____6492 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____6492 with
                            | (uu____6493,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____6497 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____6504 =
                                         let uu____6505 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____6505.FStar_Syntax_Syntax.n in
                                       match uu____6504 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____6510,uu____6511))
                                           ->
                                           let uu____6520 =
                                             let uu____6521 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____6521.FStar_Syntax_Syntax.n in
                                           (match uu____6520 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____6526,msrc,uu____6528))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____6537 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                Some uu____6537
                                            | uu____6538 -> None)
                                       | uu____6539 -> None in
                                     let uu____6540 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____6540 with
                                      | Some e ->
                                          let lb1 =
                                            let uu___175_6544 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___175_6544.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___175_6544.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___175_6544.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Syntax_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____6545 =
                                            FStar_List.tl stack1 in
                                          let uu____6546 =
                                            let uu____6547 =
                                              let uu____6550 =
                                                let uu____6551 =
                                                  let uu____6559 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____6559) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____6551 in
                                              FStar_Syntax_Syntax.mk
                                                uu____6550 in
                                            uu____6547 None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____6545 uu____6546
                                      | None  ->
                                          let uu____6576 =
                                            let uu____6577 = is_return body in
                                            match uu____6577 with
                                            | Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____6580;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____6581;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____6582;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____6587 -> false in
                                          if uu____6576
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
                                               let uu____6607 =
                                                 let uu____6610 =
                                                   let uu____6611 =
                                                     let uu____6626 =
                                                       let uu____6628 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____6628] in
                                                     (uu____6626, body1,
                                                       (Some
                                                          (FStar_Util.Inr
                                                             (m1, [])))) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____6611 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____6610 in
                                               uu____6607 None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____6661 =
                                                 let uu____6662 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____6662.FStar_Syntax_Syntax.n in
                                               match uu____6661 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____6668::uu____6669::[])
                                                   ->
                                                   let uu____6675 =
                                                     let uu____6678 =
                                                       let uu____6679 =
                                                         let uu____6684 =
                                                           let uu____6686 =
                                                             let uu____6687 =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____6687 in
                                                           let uu____6688 =
                                                             let uu____6690 =
                                                               let uu____6691
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____6691 in
                                                             [uu____6690] in
                                                           uu____6686 ::
                                                             uu____6688 in
                                                         (bind1, uu____6684) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____6679 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____6678 in
                                                   uu____6675 None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____6703 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____6709 =
                                                 let uu____6712 =
                                                   let uu____6713 =
                                                     let uu____6723 =
                                                       let uu____6725 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____6726 =
                                                         let uu____6728 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____6729 =
                                                           let uu____6731 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____6732 =
                                                             let uu____6734 =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____6735 =
                                                               let uu____6737
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____6738
                                                                 =
                                                                 let uu____6740
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____6740] in
                                                               uu____6737 ::
                                                                 uu____6738 in
                                                             uu____6734 ::
                                                               uu____6735 in
                                                           uu____6731 ::
                                                             uu____6732 in
                                                         uu____6728 ::
                                                           uu____6729 in
                                                       uu____6725 ::
                                                         uu____6726 in
                                                     (bind_inst, uu____6723) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____6713 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____6712 in
                                               uu____6709 None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____6752 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____6752 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____6770 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____6770 with
                            | (uu____6771,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____6794 =
                                        let uu____6795 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____6795.FStar_Syntax_Syntax.n in
                                      match uu____6794 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____6801) -> t4
                                      | uu____6806 -> head2 in
                                    let uu____6807 =
                                      let uu____6808 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____6808.FStar_Syntax_Syntax.n in
                                    match uu____6807 with
                                    | FStar_Syntax_Syntax.Tm_fvar x -> Some x
                                    | uu____6813 -> None in
                                  let uu____6814 = maybe_extract_fv head2 in
                                  match uu____6814 with
                                  | Some x when
                                      let uu____6820 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____6820
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____6824 =
                                          maybe_extract_fv head3 in
                                        match uu____6824 with
                                        | Some uu____6827 -> Some true
                                        | uu____6828 -> Some false in
                                      (head3, action_unfolded)
                                  | uu____6831 -> (head2, None) in
                                ((let is_arg_impure uu____6842 =
                                    match uu____6842 with
                                    | (e,q) ->
                                        let uu____6847 =
                                          let uu____6848 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____6848.FStar_Syntax_Syntax.n in
                                        (match uu____6847 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____6863 -> false) in
                                  let uu____6864 =
                                    let uu____6865 =
                                      let uu____6869 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____6869 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____6865 in
                                  if uu____6864
                                  then
                                    let uu____6872 =
                                      let uu____6873 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____6873 in
                                    failwith uu____6872
                                  else ());
                                 (let uu____6875 =
                                    maybe_unfold_action head_app in
                                  match uu____6875 with
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
                                      let uu____6910 = FStar_List.tl stack1 in
                                      norm cfg env uu____6910 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____6924 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____6924 in
                           let uu____6925 = FStar_List.tl stack1 in
                           norm cfg env uu____6925 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____7008  ->
                                     match uu____7008 with
                                     | (pat,wopt,tm) ->
                                         let uu____7046 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____7046))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____7072 = FStar_List.tl stack1 in
                           norm cfg env uu____7072 tm
                       | uu____7073 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.tk = uu____7082;
                             FStar_Syntax_Syntax.pos = uu____7083;
                             FStar_Syntax_Syntax.vars = uu____7084;_},uu____7085,uu____7086))::uu____7087
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____7093 -> false in
                    if should_reify
                    then
                      let uu____7094 = FStar_List.tl stack1 in
                      let uu____7095 =
                        let uu____7096 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____7096 in
                      norm cfg env uu____7094 uu____7095
                    else
                      (let uu____7098 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____7098
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___176_7104 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___176_7104.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___176_7104.primitive_steps)
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
                | uu____7110 ->
                    (match stack1 with
                     | uu____7111::uu____7112 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____7116)
                              -> norm cfg env ((Meta (m, r)) :: stack1) head1
                          | FStar_Syntax_Syntax.Meta_pattern args ->
                              let args1 = norm_pattern_args cfg env args in
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_pattern args1),
                                      (t1.FStar_Syntax_Syntax.pos))) ::
                                stack1) head1
                          | uu____7131 -> norm cfg env stack1 head1)
                     | [] ->
                         let head2 = norm cfg env [] head1 in
                         let m1 =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               let uu____7141 =
                                 norm_pattern_args cfg env args in
                               FStar_Syntax_Syntax.Meta_pattern uu____7141
                           | uu____7148 -> m in
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
              let uu____7160 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____7160 with
              | (uu____7161,return_repr) ->
                  let return_inst =
                    let uu____7168 =
                      let uu____7169 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____7169.FStar_Syntax_Syntax.n in
                    match uu____7168 with
                    | FStar_Syntax_Syntax.Tm_uinst (return_tm,uu____7175::[])
                        ->
                        let uu____7181 =
                          let uu____7184 =
                            let uu____7185 =
                              let uu____7190 =
                                let uu____7192 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____7192] in
                              (return_tm, uu____7190) in
                            FStar_Syntax_Syntax.Tm_uinst uu____7185 in
                          FStar_Syntax_Syntax.mk uu____7184 in
                        uu____7181 None e.FStar_Syntax_Syntax.pos
                    | uu____7204 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____7207 =
                    let uu____7210 =
                      let uu____7211 =
                        let uu____7221 =
                          let uu____7223 = FStar_Syntax_Syntax.as_arg t in
                          let uu____7224 =
                            let uu____7226 = FStar_Syntax_Syntax.as_arg e in
                            [uu____7226] in
                          uu____7223 :: uu____7224 in
                        (return_inst, uu____7221) in
                      FStar_Syntax_Syntax.Tm_app uu____7211 in
                    FStar_Syntax_Syntax.mk uu____7210 in
                  uu____7207 None e.FStar_Syntax_Syntax.pos
            else
              (let uu____7239 = FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____7239 with
               | None  ->
                   let uu____7241 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____7241
               | Some
                   { FStar_TypeChecker_Env.msource = uu____7242;
                     FStar_TypeChecker_Env.mtarget = uu____7243;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____7244;
                         FStar_TypeChecker_Env.mlift_term = None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | Some
                   { FStar_TypeChecker_Env.msource = uu____7255;
                     FStar_TypeChecker_Env.mtarget = uu____7256;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____7257;
                         FStar_TypeChecker_Env.mlift_term = Some lift;_};_}
                   ->
                   let uu____7275 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____7275)
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
                (fun uu____7305  ->
                   match uu____7305 with
                   | (a,imp) ->
                       let uu____7312 = norm cfg env [] a in
                       (uu____7312, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___177_7327 = comp1 in
            let uu____7330 =
              let uu____7331 =
                let uu____7337 = norm cfg env [] t in
                let uu____7338 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____7337, uu____7338) in
              FStar_Syntax_Syntax.Total uu____7331 in
            {
              FStar_Syntax_Syntax.n = uu____7330;
              FStar_Syntax_Syntax.tk = (uu___177_7327.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___177_7327.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___177_7327.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___178_7353 = comp1 in
            let uu____7356 =
              let uu____7357 =
                let uu____7363 = norm cfg env [] t in
                let uu____7364 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____7363, uu____7364) in
              FStar_Syntax_Syntax.GTotal uu____7357 in
            {
              FStar_Syntax_Syntax.n = uu____7356;
              FStar_Syntax_Syntax.tk = (uu___178_7353.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___178_7353.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___178_7353.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____7395  ->
                      match uu____7395 with
                      | (a,i) ->
                          let uu____7402 = norm cfg env [] a in
                          (uu____7402, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___141_7407  ->
                      match uu___141_7407 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____7411 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____7411
                      | f -> f)) in
            let uu___179_7415 = comp1 in
            let uu____7418 =
              let uu____7419 =
                let uu___180_7420 = ct in
                let uu____7421 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____7422 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____7425 = norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____7421;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___180_7420.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____7422;
                  FStar_Syntax_Syntax.effect_args = uu____7425;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____7419 in
            {
              FStar_Syntax_Syntax.n = uu____7418;
              FStar_Syntax_Syntax.tk = (uu___179_7415.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___179_7415.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___179_7415.FStar_Syntax_Syntax.vars)
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
            (let uu___181_7442 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___181_7442.tcenv);
               delta_level = (uu___181_7442.delta_level);
               primitive_steps = (uu___181_7442.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____7447 = norm1 t in
          FStar_Syntax_Util.non_informative uu____7447 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____7450 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___182_7464 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.tk = (uu___182_7464.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___182_7464.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___182_7464.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____7474 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____7474
            then
              let ct1 =
                match downgrade_ghost_effect_name
                        ct.FStar_Syntax_Syntax.effect_name
                with
                | Some pure_eff ->
                    let uu___183_7479 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___183_7479.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___183_7479.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___183_7479.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___183_7479.FStar_Syntax_Syntax.flags)
                    }
                | None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___184_7481 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___184_7481.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Syntax_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___184_7481.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___184_7481.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___184_7481.FStar_Syntax_Syntax.flags)
                    } in
              let uu___185_7482 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.tk =
                  (uu___185_7482.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___185_7482.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___185_7482.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____7488 -> c
and norm_binder:
  cfg ->
    env ->
      FStar_Syntax_Syntax.binder ->
        (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  =
  fun cfg  ->
    fun env  ->
      fun uu____7491  ->
        match uu____7491 with
        | (x,imp) ->
            let uu____7494 =
              let uu___186_7495 = x in
              let uu____7496 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___186_7495.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___186_7495.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____7496
              } in
            (uu____7494, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____7502 =
          FStar_List.fold_left
            (fun uu____7509  ->
               fun b  ->
                 match uu____7509 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____7502 with | (nbs,uu____7526) -> FStar_List.rev nbs
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
            let uu____7543 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
            if uu____7543
            then
              let t = norm cfg env [] lc.FStar_Syntax_Syntax.res_typ in
              let uu____7548 = FStar_Syntax_Util.is_total_lcomp lc in
              (if uu____7548
               then
                 let uu____7552 =
                   let uu____7555 =
                     let uu____7556 =
                       let uu____7559 = FStar_Syntax_Syntax.mk_Total t in
                       FStar_Syntax_Util.comp_set_flags uu____7559 flags in
                     FStar_Syntax_Util.lcomp_of_comp uu____7556 in
                   FStar_Util.Inl uu____7555 in
                 Some uu____7552
               else
                 (let uu____7563 =
                    let uu____7566 =
                      let uu____7567 =
                        let uu____7570 = FStar_Syntax_Syntax.mk_GTotal t in
                        FStar_Syntax_Util.comp_set_flags uu____7570 flags in
                      FStar_Syntax_Util.lcomp_of_comp uu____7567 in
                    FStar_Util.Inl uu____7566 in
                  Some uu____7563))
            else
              Some
                (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags))
        | uu____7583 -> lopt
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
              ((let uu____7595 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____7595
                then
                  let uu____7596 = FStar_Syntax_Print.term_to_string tm in
                  let uu____7597 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2 "Normalized %s to %s\n" uu____7596
                    uu____7597
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___187_7608 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___187_7608.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____7628  ->
                    let uu____7629 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____7629);
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
              let uu____7666 =
                let uu___188_7667 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___188_7667.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___188_7667.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___188_7667.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____7666
          | (Arg (Univ _,_,_))::_|(Arg (Dummy ,_,_))::_ ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____7689),aq,r))::stack2 ->
              (log cfg
                 (fun uu____7705  ->
                    let uu____7706 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____7706);
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
                 (let uu____7717 = FStar_ST.read m in
                  match uu____7717 with
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
                  | Some (uu____7743,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq) None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.extend_app head1 (t, aq) None r in
              let uu____7765 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____7765
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____7772  ->
                    let uu____7773 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____7773);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____7778 =
                  log cfg
                    (fun uu____7780  ->
                       let uu____7781 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____7782 =
                         let uu____7783 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____7790  ->
                                   match uu____7790 with
                                   | (p,uu____7796,uu____7797) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____7783
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____7781 uu____7782);
                  (let whnf = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___142_7807  ->
                               match uu___142_7807 with
                               | FStar_TypeChecker_Env.Inlining 
                                 |FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____7808 -> false)) in
                     let steps' =
                       let uu____7811 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____7811
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___189_7814 = cfg in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___189_7814.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___189_7814.primitive_steps)
                     } in
                   let norm_or_whnf env2 t1 =
                     if whnf
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____7848 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_disj [] ->
                         failwith "Impossible"
                     | FStar_Syntax_Syntax.Pat_disj (hd1::tl1) ->
                         let uu____7868 = norm_pat env2 hd1 in
                         (match uu____7868 with
                          | (hd2,env') ->
                              let tl2 =
                                FStar_All.pipe_right tl1
                                  (FStar_List.map
                                     (fun p1  ->
                                        let uu____7904 = norm_pat env2 p1 in
                                        Prims.fst uu____7904)) in
                              ((let uu___190_7916 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_disj (hd2 ::
                                       tl2));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___190_7916.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___190_7916.FStar_Syntax_Syntax.p)
                                }), env'))
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____7933 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____7967  ->
                                   fun uu____7968  ->
                                     match (uu____7967, uu____7968) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____8033 = norm_pat env3 p1 in
                                         (match uu____8033 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____7933 with
                          | (pats1,env3) ->
                              ((let uu___191_8099 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___191_8099.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___191_8099.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___192_8113 = x in
                           let uu____8114 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___192_8113.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___192_8113.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____8114
                           } in
                         ((let uu___193_8120 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___193_8120.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___193_8120.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___194_8125 = x in
                           let uu____8126 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___194_8125.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___194_8125.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____8126
                           } in
                         ((let uu___195_8132 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___195_8132.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___195_8132.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___196_8142 = x in
                           let uu____8143 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___196_8142.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___196_8142.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____8143
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___197_8150 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.ty =
                               (uu___197_8150.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___197_8150.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf -> branches
                     | uu____8154 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____8157 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____8157 with
                                 | (p,wopt,e) ->
                                     let uu____8175 = norm_pat env1 p in
                                     (match uu____8175 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | None  -> None
                                            | Some w ->
                                                let uu____8199 =
                                                  norm_or_whnf env2 w in
                                                Some uu____8199 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____8204 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____8204) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____8214) -> is_cons h
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
                  | uu____8225 -> false in
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
                  let uu____8324 = FStar_Syntax_Util.head_and_args scrutinee2 in
                  match uu____8324 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_disj ps ->
                           let mopt =
                             FStar_Util.find_map ps
                               (fun p1  ->
                                  let m = matches_pat scrutinee2 p1 in
                                  match m with
                                  | FStar_Util.Inl uu____8381 -> Some m
                                  | FStar_Util.Inr (true ) -> Some m
                                  | FStar_Util.Inr (false ) -> None) in
                           (match mopt with
                            | None  -> FStar_Util.Inr false
                            | Some m -> m)
                       | FStar_Syntax_Syntax.Pat_var _
                         |FStar_Syntax_Syntax.Pat_wild _ ->
                           FStar_Util.Inl [scrutinee2]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____8412 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____8424 ->
                                let uu____8425 =
                                  let uu____8426 = is_cons head1 in
                                  Prims.op_Negation uu____8426 in
                                FStar_Util.Inr uu____8425)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____8440 =
                             let uu____8441 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____8441.FStar_Syntax_Syntax.n in
                           (match uu____8440 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____8448 ->
                                let uu____8449 =
                                  let uu____8450 = is_cons head1 in
                                  Prims.op_Negation uu____8450 in
                                FStar_Util.Inr uu____8449))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____8484)::rest_a,(p1,uu____8487)::rest_p) ->
                      let uu____8515 = matches_pat t1 p1 in
                      (match uu____8515 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____8529 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____8600 = matches_pat scrutinee1 p1 in
                      (match uu____8600 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____8610  ->
                                 let uu____8611 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____8612 =
                                   let uu____8613 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____8613
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____8611 uu____8612);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____8622 =
                                        let uu____8623 =
                                          let uu____8633 =
                                            FStar_Util.mk_ref (Some ([], t1)) in
                                          ([], t1, uu____8633, false) in
                                        Clos uu____8623 in
                                      uu____8622 :: env2) env1 s in
                             let uu____8656 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____8656))) in
                let uu____8657 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____8657
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___143_8671  ->
                match uu___143_8671 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | uu____8674 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____8678 -> d in
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
            let uu___198_8698 = config s e in
            {
              steps = (uu___198_8698.steps);
              tcenv = (uu___198_8698.tcenv);
              delta_level = (uu___198_8698.delta_level);
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
      fun t  -> let uu____8717 = config s e in norm_comp uu____8717 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  -> let uu____8724 = config [] env in norm_universe uu____8724 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun c  ->
      let uu____8731 = config [] env in ghost_to_pure_aux uu____8731 [] c
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
        let uu____8743 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____8743 in
      let uu____8744 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____8744
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | Some pure_eff ->
            let uu___199_8746 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___199_8746.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___199_8746.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____8747  ->
                    let uu____8748 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____8748))
            }
        | None  -> lc
      else lc
let term_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun env  ->
    fun t  ->
      let uu____8756 = normalize [AllowUnboundUniverses] env t in
      FStar_Syntax_Print.term_to_string uu____8756
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let uu____8763 =
        let uu____8764 = config [AllowUnboundUniverses] env in
        norm_comp uu____8764 [] c in
      FStar_Syntax_Print.comp_to_string uu____8763
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
                   let uu____8801 =
                     let uu____8802 =
                       let uu____8807 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____8807) in
                     FStar_Syntax_Syntax.Tm_refine uu____8802 in
                   mk uu____8801 t01.FStar_Syntax_Syntax.pos
               | uu____8812 -> t2)
          | uu____8813 -> t2 in
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
        let uu____8829 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____8829 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____8845 ->
                 let uu____8849 = FStar_Syntax_Util.abs_formals e in
                 (match uu____8849 with
                  | (actuals,uu____8860,uu____8861) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____8883 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____8883 with
                         | (binders,args) ->
                             let uu____8893 =
                               (FStar_Syntax_Syntax.mk_Tm_app e args) None
                                 e.FStar_Syntax_Syntax.pos in
                             let uu____8898 =
                               let uu____8905 =
                                 FStar_All.pipe_right
                                   (FStar_Syntax_Util.lcomp_of_comp c)
                                   (fun _0_33  -> FStar_Util.Inl _0_33) in
                               FStar_All.pipe_right uu____8905
                                 (fun _0_34  -> Some _0_34) in
                             FStar_Syntax_Util.abs binders uu____8893
                               uu____8898)))
let eta_expand:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____8941 =
        let uu____8945 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
        (uu____8945, (t.FStar_Syntax_Syntax.n)) in
      match uu____8941 with
      | (Some sort,uu____8952) ->
          let uu____8954 = mk sort t.FStar_Syntax_Syntax.pos in
          eta_expand_with_type env t uu____8954
      | (uu____8955,FStar_Syntax_Syntax.Tm_name x) ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____8959 ->
          let uu____8963 = FStar_Syntax_Util.head_and_args t in
          (match uu____8963 with
           | (head1,args) ->
               let uu____8989 =
                 let uu____8990 = FStar_Syntax_Subst.compress head1 in
                 uu____8990.FStar_Syntax_Syntax.n in
               (match uu____8989 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____8993,thead) ->
                    let uu____9007 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____9007 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____9038 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___200_9042 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___200_9042.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___200_9042.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___200_9042.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___200_9042.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___200_9042.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___200_9042.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ = None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___200_9042.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___200_9042.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___200_9042.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___200_9042.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___200_9042.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___200_9042.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___200_9042.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___200_9042.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___200_9042.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___200_9042.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___200_9042.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___200_9042.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___200_9042.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___200_9042.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___200_9042.FStar_TypeChecker_Env.qname_and_index)
                                 }) t in
                            match uu____9038 with
                            | (uu____9043,ty,uu____9045) ->
                                eta_expand_with_type env t ty))
                | uu____9046 ->
                    let uu____9047 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___201_9051 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___201_9051.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___201_9051.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___201_9051.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___201_9051.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___201_9051.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___201_9051.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ = None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___201_9051.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___201_9051.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___201_9051.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___201_9051.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___201_9051.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___201_9051.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___201_9051.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___201_9051.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___201_9051.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___201_9051.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___201_9051.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___201_9051.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___201_9051.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___201_9051.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___201_9051.FStar_TypeChecker_Env.qname_and_index)
                         }) t in
                    (match uu____9047 with
                     | (uu____9052,ty,uu____9054) ->
                         eta_expand_with_type env t ty)))