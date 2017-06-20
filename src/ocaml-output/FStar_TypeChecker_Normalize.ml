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
  fun uu___137_265  ->
    match uu___137_265 with
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
  FStar_Syntax_Syntax.residual_comp option* FStar_Range.range)
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
    match projectee with | Arg _0 -> true | uu____410 -> false
let __proj__Arg__item___0:
  stack_elt -> (closure* FStar_Syntax_Syntax.aqual* FStar_Range.range) =
  fun projectee  -> match projectee with | Arg _0 -> _0
let uu___is_UnivArgs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____436 -> false
let __proj__UnivArgs__item___0:
  stack_elt -> (FStar_Syntax_Syntax.universe Prims.list* FStar_Range.range) =
  fun projectee  -> match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____462 -> false
let __proj__MemoLazy__item___0:
  stack_elt -> (env* FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo =
  fun projectee  -> match projectee with | MemoLazy _0 -> _0
let uu___is_Match: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____491 -> false
let __proj__Match__item___0: stack_elt -> (env* branches* FStar_Range.range)
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Abs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____520 -> false
let __proj__Abs__item___0:
  stack_elt ->
    (env* FStar_Syntax_Syntax.binders* env* FStar_Syntax_Syntax.residual_comp
      option* FStar_Range.range)
  = fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____555 -> false
let __proj__App__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.aqual* FStar_Range.range)
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Meta: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____580 -> false
let __proj__Meta__item___0:
  stack_elt -> (FStar_Syntax_Syntax.metadata* FStar_Range.range) =
  fun projectee  -> match projectee with | Meta _0 -> _0
let uu___is_Let: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____604 -> false
let __proj__Let__item___0:
  stack_elt ->
    (env* FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.letbinding*
      FStar_Range.range)
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Steps: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Steps _0 -> true | uu____635 -> false
let __proj__Steps__item___0:
  stack_elt ->
    (steps* primitive_step Prims.list* FStar_TypeChecker_Env.delta_level
      Prims.list)
  = fun projectee  -> match projectee with | Steps _0 -> _0
let uu___is_Debug: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____664 -> false
let __proj__Debug__item___0: stack_elt -> FStar_Syntax_Syntax.term =
  fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list
let mk t r = FStar_Syntax_Syntax.mk t None r
let set_memo r t =
  let uu____720 = FStar_ST.read r in
  match uu____720 with
  | Some uu____725 -> failwith "Unexpected set_memo: thunk already evaluated"
  | None  -> FStar_ST.write r (Some t)
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____735 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____735 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___138_741  ->
    match uu___138_741 with
    | Arg (c,uu____743,uu____744) ->
        let uu____745 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____745
    | MemoLazy uu____746 -> "MemoLazy"
    | Abs (uu____750,bs,uu____752,uu____753,uu____754) ->
        let uu____757 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____757
    | UnivArgs uu____764 -> "UnivArgs"
    | Match uu____768 -> "Match"
    | App (t,uu____773,uu____774) ->
        let uu____775 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____775
    | Meta (m,uu____777) -> "Meta"
    | Let uu____778 -> "Let"
    | Steps (uu____783,uu____784,uu____785) -> "Steps"
    | Debug t ->
        let uu____791 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____791
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____798 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____798 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____814 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____814 then f () else ()
let is_empty uu___139_825 =
  match uu___139_825 with | [] -> true | uu____827 -> false
let lookup_bvar env x =
  try FStar_List.nth env x.FStar_Syntax_Syntax.index
  with
  | uu____848 ->
      let uu____849 =
        let uu____850 = FStar_Syntax_Print.db_to_string x in
        FStar_Util.format1 "Failed to find %s\n" uu____850 in
      failwith uu____849
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
          let uu____885 =
            FStar_List.fold_left
              (fun uu____894  ->
                 fun u1  ->
                   match uu____894 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____909 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____909 with
                        | (k_u,n1) ->
                            let uu____918 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____918
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____885 with
          | (uu____928,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____944 = FStar_List.nth env x in
                 match uu____944 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____947 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____951 ->
                   let uu____952 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____952
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____956 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____959 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____964 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____964 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____975 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____975 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____980 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____983 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____983 with
                                  | (uu____986,m) -> n1 <= m)) in
                        if uu____980 then rest1 else us1
                    | uu____990 -> us1)
               | uu____993 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____996 = aux u3 in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____996 in
        let uu____998 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____998
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1000 = aux u in
           match uu____1000 with
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
          (fun uu____1088  ->
             let uu____1089 = FStar_Syntax_Print.tag_of_term t in
             let uu____1090 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1089
               uu____1090);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1091 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1094 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____1109 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____1110 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____1111 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____1112 -> t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____1122 =
                    let uu____1123 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____1123 in
                  mk uu____1122 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____1130 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____1130
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____1132 = lookup_bvar env x in
                  (match uu____1132 with
                   | Univ uu____1133 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____1137) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____1195 = closures_as_binders_delayed cfg env bs in
                  (match uu____1195 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____1215 =
                         let uu____1216 =
                           let uu____1226 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____1226) in
                         FStar_Syntax_Syntax.Tm_abs uu____1216 in
                       mk uu____1215 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____1246 = closures_as_binders_delayed cfg env bs in
                  (match uu____1246 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____1277 =
                    let uu____1284 =
                      let uu____1288 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____1288] in
                    closures_as_binders_delayed cfg env uu____1284 in
                  (match uu____1277 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____1302 =
                         let uu____1303 =
                           let uu____1308 =
                             let uu____1309 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____1309
                               FStar_Pervasives.fst in
                           (uu____1308, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____1303 in
                       mk uu____1302 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____1377 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____1377
                    | FStar_Util.Inr c ->
                        let uu____1391 = close_comp cfg env c in
                        FStar_Util.Inr uu____1391 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____1406 =
                    let uu____1407 =
                      let uu____1425 = closure_as_term_delayed cfg env t11 in
                      (uu____1425, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____1407 in
                  mk uu____1406 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____1463 =
                    let uu____1464 =
                      let uu____1469 = closure_as_term_delayed cfg env t' in
                      let uu____1472 =
                        let uu____1473 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____1473 in
                      (uu____1469, uu____1472) in
                    FStar_Syntax_Syntax.Tm_meta uu____1464 in
                  mk uu____1463 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____1515 =
                    let uu____1516 =
                      let uu____1521 = closure_as_term_delayed cfg env t' in
                      let uu____1524 =
                        let uu____1525 =
                          let uu____1530 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____1530) in
                        FStar_Syntax_Syntax.Meta_monadic uu____1525 in
                      (uu____1521, uu____1524) in
                    FStar_Syntax_Syntax.Tm_meta uu____1516 in
                  mk uu____1515 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____1549 =
                    let uu____1550 =
                      let uu____1555 = closure_as_term_delayed cfg env t' in
                      let uu____1558 =
                        let uu____1559 =
                          let uu____1565 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____1565) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____1559 in
                      (uu____1555, uu____1558) in
                    FStar_Syntax_Syntax.Tm_meta uu____1550 in
                  mk uu____1549 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____1578 =
                    let uu____1579 =
                      let uu____1584 = closure_as_term_delayed cfg env t' in
                      (uu____1584, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____1579 in
                  mk uu____1578 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____1605  -> Dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let body1 =
                    match lb.FStar_Syntax_Syntax.lbname with
                    | FStar_Util.Inr uu____1616 -> body
                    | FStar_Util.Inl uu____1617 ->
                        closure_as_term cfg (Dummy :: env0) body in
                  let lb1 =
                    let uu___153_1619 = lb in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___153_1619.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___153_1619.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = typ;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___153_1619.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = def
                    } in
                  mk (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((uu____1626,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____1650  -> fun env2  -> Dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____1655 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____1655
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____1659  -> fun env2  -> Dummy :: env2) lbs
                          env_univs in
                    let uu___154_1662 = lb in
                    let uu____1663 =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let uu____1666 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___154_1662.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___154_1662.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = uu____1663;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___154_1662.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____1666
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____1677  -> fun env1  -> Dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____1732 =
                    match uu____1732 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____1778 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____1794 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____1828  ->
                                        fun uu____1829  ->
                                          match (uu____1828, uu____1829) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____1894 =
                                                norm_pat env3 p1 in
                                              (match uu____1894 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____1794 with
                               | (pats1,env3) ->
                                   ((let uu___155_1960 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.ty =
                                         (uu___155_1960.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___155_1960.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___156_1974 = x in
                                let uu____1975 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___156_1974.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___156_1974.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1975
                                } in
                              ((let uu___157_1981 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___157_1981.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___157_1981.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___158_1986 = x in
                                let uu____1987 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___158_1986.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___158_1986.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1987
                                } in
                              ((let uu___159_1993 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___159_1993.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___159_1993.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___160_2003 = x in
                                let uu____2004 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___160_2003.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___160_2003.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____2004
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___161_2011 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___161_2011.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___161_2011.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____2014 = norm_pat env1 pat in
                        (match uu____2014 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | None  -> None
                               | Some w ->
                                   let uu____2038 =
                                     closure_as_term cfg env2 w in
                                   Some uu____2038 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____2043 =
                    let uu____2044 =
                      let uu____2060 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____2060) in
                    FStar_Syntax_Syntax.Tm_match uu____2044 in
                  mk uu____2043 t1.FStar_Syntax_Syntax.pos))
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
        | uu____2113 -> closure_as_term cfg env t
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
        | uu____2129 ->
            FStar_List.map
              (fun uu____2139  ->
                 match uu____2139 with
                 | (x,imp) ->
                     let uu____2154 = closure_as_term_delayed cfg env x in
                     (uu____2154, imp)) args
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
        let uu____2166 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____2190  ->
                  fun uu____2191  ->
                    match (uu____2190, uu____2191) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___162_2235 = b in
                          let uu____2236 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___162_2235.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___162_2235.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____2236
                          } in
                        let env2 = Dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____2166 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____2283 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____2295 = closure_as_term_delayed cfg env t in
                 let uu____2296 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____2295 uu____2296
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____2306 = closure_as_term_delayed cfg env t in
                 let uu____2307 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____2306 uu____2307
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
                        (fun uu___140_2323  ->
                           match uu___140_2323 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____2327 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____2327
                           | f -> f)) in
                 let uu____2331 =
                   let uu___163_2332 = c1 in
                   let uu____2333 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____2333;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___163_2332.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____2331)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags  ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___141_2338  ->
            match uu___141_2338 with
            | FStar_Syntax_Syntax.DECREASES uu____2339 -> false
            | uu____2342 -> true))
and close_lcomp_opt:
  cfg ->
    closure Prims.list ->
      FStar_Syntax_Syntax.residual_comp option ->
        FStar_Syntax_Syntax.residual_comp option
  =
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | Some rc ->
            let flags =
              FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                (FStar_List.filter
                   (fun uu___142_2354  ->
                      match uu___142_2354 with
                      | FStar_Syntax_Syntax.DECREASES uu____2355 -> false
                      | uu____2358 -> true)) in
            let rc1 =
              let uu___164_2360 = rc in
              let uu____2361 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___164_2360.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____2361;
                FStar_Syntax_Syntax.residual_flags = flags
              } in
            Some rc1
        | uu____2367 -> lopt
let built_in_primitive_steps: primitive_step Prims.list =
  let const_as_tm c p = mk (FStar_Syntax_Syntax.Tm_constant c) p in
  let int_as_const p i =
    let uu____2386 =
      let uu____2387 =
        let uu____2393 = FStar_Util.string_of_int i in (uu____2393, None) in
      FStar_Const.Const_int uu____2387 in
    const_as_tm uu____2386 p in
  let bool_as_const p b = const_as_tm (FStar_Const.Const_bool b) p in
  let string_as_const p b =
    const_as_tm
      (FStar_Const.Const_string ((FStar_Util.bytes_of_string b), p)) p in
  let arg_as_int uu____2420 =
    match uu____2420 with
    | (a,uu____2425) ->
        let uu____2427 =
          let uu____2428 = FStar_Syntax_Subst.compress a in
          uu____2428.FStar_Syntax_Syntax.n in
        (match uu____2427 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i,None ))
             ->
             let uu____2438 = FStar_Util.int_of_string i in Some uu____2438
         | uu____2439 -> None) in
  let arg_as_bounded_int uu____2448 =
    match uu____2448 with
    | (a,uu____2455) ->
        let uu____2459 =
          let uu____2460 = FStar_Syntax_Subst.compress a in
          uu____2460.FStar_Syntax_Syntax.n in
        (match uu____2459 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.tk = uu____2467;
                FStar_Syntax_Syntax.pos = uu____2468;
                FStar_Syntax_Syntax.vars = uu____2469;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,None ));
                                                            FStar_Syntax_Syntax.tk
                                                              = uu____2471;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____2472;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____2473;_},uu____2474)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____2505 =
               let uu____2508 = FStar_Util.int_of_string i in
               (fv1, uu____2508) in
             Some uu____2505
         | uu____2511 -> None) in
  let arg_as_bool uu____2520 =
    match uu____2520 with
    | (a,uu____2525) ->
        let uu____2527 =
          let uu____2528 = FStar_Syntax_Subst.compress a in
          uu____2528.FStar_Syntax_Syntax.n in
        (match uu____2527 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
             Some b
         | uu____2533 -> None) in
  let arg_as_char uu____2540 =
    match uu____2540 with
    | (a,uu____2545) ->
        let uu____2547 =
          let uu____2548 = FStar_Syntax_Subst.compress a in
          uu____2548.FStar_Syntax_Syntax.n in
        (match uu____2547 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
             Some c
         | uu____2553 -> None) in
  let arg_as_string uu____2560 =
    match uu____2560 with
    | (a,uu____2565) ->
        let uu____2567 =
          let uu____2568 = FStar_Syntax_Subst.compress a in
          uu____2568.FStar_Syntax_Syntax.n in
        (match uu____2567 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (bytes,uu____2573)) -> Some (FStar_Util.string_of_bytes bytes)
         | uu____2576 -> None) in
  let arg_as_list f uu____2597 =
    match uu____2597 with
    | (a,uu____2606) ->
        let rec sequence l =
          match l with
          | [] -> Some []
          | (None )::uu____2625 -> None
          | (Some x)::xs ->
              let uu____2635 = sequence xs in
              (match uu____2635 with
               | None  -> None
               | Some xs' -> Some (x :: xs')) in
        let uu____2646 = FStar_Syntax_Util.list_elements a in
        (match uu____2646 with
         | None  -> None
         | Some elts ->
             let uu____2656 =
               FStar_List.map
                 (fun x  ->
                    let uu____2661 = FStar_Syntax_Syntax.as_arg x in
                    f uu____2661) elts in
             sequence uu____2656) in
  let lift_unary f aopts =
    match aopts with
    | (Some a)::[] -> let uu____2691 = f a in Some uu____2691
    | uu____2692 -> None in
  let lift_binary f aopts =
    match aopts with
    | (Some a0)::(Some a1)::[] -> let uu____2731 = f a0 a1 in Some uu____2731
    | uu____2732 -> None in
  let unary_op as_a f r args =
    let uu____2776 = FStar_List.map as_a args in lift_unary (f r) uu____2776 in
  let binary_op as_a f r args =
    let uu____2826 = FStar_List.map as_a args in lift_binary (f r) uu____2826 in
  let as_primitive_step uu____2843 =
    match uu____2843 with
    | (l,arity,f) ->
        { name = l; arity; strong_reduction_ok = true; interpretation = f } in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  -> fun x  -> let uu____2881 = f x in int_as_const r uu____2881) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2904 = f x y in int_as_const r uu____2904) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  -> fun x  -> let uu____2921 = f x in bool_as_const r uu____2921) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2944 = f x y in bool_as_const r uu____2944) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2967 = f x y in string_as_const r uu____2967) in
  let list_of_string' rng s =
    let name l =
      let uu____2981 =
        let uu____2982 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            None in
        FStar_Syntax_Syntax.Tm_fvar uu____2982 in
      mk uu____2981 rng in
    let char_t = name FStar_Syntax_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____2992 =
      let uu____2994 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____2994 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____2992 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Const.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in int_as_const rng r in
  let string_concat' rng args =
    match args with
    | a1::a2::[] ->
        let uu____3048 = arg_as_string a1 in
        (match uu____3048 with
         | Some s1 ->
             let uu____3052 = arg_as_list arg_as_string a2 in
             (match uu____3052 with
              | Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____3060 = string_as_const rng r in Some uu____3060
              | uu____3061 -> None)
         | uu____3064 -> None)
    | uu____3066 -> None in
  let string_of_int1 rng i =
    let uu____3077 = FStar_Util.string_of_int i in
    string_as_const rng uu____3077 in
  let string_of_bool1 rng b =
    string_as_const rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____3093 = FStar_Util.string_of_int i in
    string_as_const rng uu____3093 in
  let string_of_bool2 rng b =
    string_as_const rng (if b then "true" else "false") in
  let basic_ops =
    let uu____3112 =
      let uu____3122 =
        let uu____3132 =
          let uu____3142 =
            let uu____3152 =
              let uu____3162 =
                let uu____3172 =
                  let uu____3182 =
                    let uu____3192 =
                      let uu____3202 =
                        let uu____3212 =
                          let uu____3222 =
                            let uu____3232 =
                              let uu____3242 =
                                let uu____3252 =
                                  let uu____3262 =
                                    let uu____3272 =
                                      let uu____3282 =
                                        let uu____3291 =
                                          FStar_Syntax_Const.p2l
                                            ["FStar";
                                            "String";
                                            "list_of_string"] in
                                        (uu____3291, (Prims.parse_int "1"),
                                          (unary_op arg_as_string
                                             list_of_string')) in
                                      let uu____3297 =
                                        let uu____3307 =
                                          let uu____3316 =
                                            FStar_Syntax_Const.p2l
                                              ["FStar";
                                              "String";
                                              "string_of_list"] in
                                          (uu____3316, (Prims.parse_int "1"),
                                            (unary_op
                                               (arg_as_list arg_as_char)
                                               string_of_list')) in
                                        let uu____3323 =
                                          let uu____3333 =
                                            let uu____3345 =
                                              FStar_Syntax_Const.p2l
                                                ["FStar"; "String"; "concat"] in
                                            (uu____3345,
                                              (Prims.parse_int "2"),
                                              string_concat') in
                                          [uu____3333] in
                                        uu____3307 :: uu____3323 in
                                      uu____3282 :: uu____3297 in
                                    (FStar_Syntax_Const.string_compare,
                                      (Prims.parse_int "2"),
                                      (binary_op arg_as_string
                                         string_compare'))
                                      :: uu____3272 in
                                  (FStar_Syntax_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_bool string_of_bool2))
                                    :: uu____3262 in
                                (FStar_Syntax_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (unary_op arg_as_int string_of_int2)) ::
                                  uu____3252 in
                              (FStar_Syntax_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____3242 in
                            (FStar_Syntax_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____3232 in
                          (FStar_Syntax_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____3222 in
                        (FStar_Syntax_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____3212 in
                      (FStar_Syntax_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____3202 in
                    (FStar_Syntax_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
                      :: uu____3192 in
                  (FStar_Syntax_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____3182 in
                (FStar_Syntax_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____3172 in
              (FStar_Syntax_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____3162 in
            (FStar_Syntax_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____3152 in
          (FStar_Syntax_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____3142 in
        (FStar_Syntax_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____3132 in
      (FStar_Syntax_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____3122 in
    (FStar_Syntax_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____3112 in
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
      let uu____3669 =
        let uu____3670 =
          let uu____3671 = FStar_Syntax_Syntax.as_arg c in [uu____3671] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____3670 in
      uu____3669 None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____3695 =
              let uu____3704 = FStar_Syntax_Const.p2l ["FStar"; m; "add"] in
              (uu____3704, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____3713  ->
                        fun uu____3714  ->
                          match (uu____3713, uu____3714) with
                          | ((int_to_t1,x),(uu____3725,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____3731 =
              let uu____3741 =
                let uu____3750 = FStar_Syntax_Const.p2l ["FStar"; m; "sub"] in
                (uu____3750, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____3759  ->
                          fun uu____3760  ->
                            match (uu____3759, uu____3760) with
                            | ((int_to_t1,x),(uu____3771,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____3777 =
                let uu____3787 =
                  let uu____3796 = FStar_Syntax_Const.p2l ["FStar"; m; "mul"] in
                  (uu____3796, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____3805  ->
                            fun uu____3806  ->
                              match (uu____3805, uu____3806) with
                              | ((int_to_t1,x),(uu____3817,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____3787] in
              uu____3741 :: uu____3777 in
            uu____3695 :: uu____3731)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_bool neg rng args =
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) rng in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) rng in
    match args with
    | (_typ,uu____3892)::(a1,uu____3894)::(a2,uu____3896)::[] ->
        let uu____3925 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3925 with
         | FStar_Syntax_Util.Equal  -> Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  -> Some (if neg then tru else fal)
         | uu____3937 -> None)
    | uu____3938 -> failwith "Unexpected number of arguments" in
  let interp_prop r args =
    match args with
    | (_typ,uu____3951)::(a1,uu____3953)::(a2,uu____3955)::[] ->
        let uu____3984 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3984 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___165_3988 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___165_3988.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___165_3988.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___165_3988.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___166_3995 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___166_3995.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___166_3995.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___166_3995.FStar_Syntax_Syntax.vars)
                })
         | uu____4000 -> None)
    | (_typ,uu____4002)::uu____4003::(a1,uu____4005)::(a2,uu____4007)::[] ->
        let uu____4044 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4044 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___165_4048 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___165_4048.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___165_4048.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___165_4048.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___166_4055 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___166_4055.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___166_4055.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___166_4055.FStar_Syntax_Syntax.vars)
                })
         | uu____4060 -> None)
    | uu____4061 -> failwith "Unexpected number of arguments" in
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
      let uu____4075 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops cfg.steps) in
      if uu____4075
      then tm
      else
        (let uu____4077 = FStar_Syntax_Util.head_and_args tm in
         match uu____4077 with
         | (head1,args) ->
             let uu____4103 =
               let uu____4104 = FStar_Syntax_Util.un_uinst head1 in
               uu____4104.FStar_Syntax_Syntax.n in
             (match uu____4103 with
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____4108 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps in
                  (match uu____4108 with
                   | None  -> tm
                   | Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then tm
                       else
                         (let uu____4123 =
                            prim_step.interpretation
                              head1.FStar_Syntax_Syntax.pos args in
                          match uu____4123 with
                          | None  -> tm
                          | Some reduced -> reduced))
              | uu____4126 -> tm))
let reduce_equality:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___167_4135 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___167_4135.tcenv);
           delta_level = (uu___167_4135.delta_level);
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
        let uu___168_4159 = t in
        {
          FStar_Syntax_Syntax.n = (uu___168_4159.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___168_4159.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___168_4159.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid ->
            Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid ->
            Some false
        | uu____4178 -> None in
      let simplify arg = ((simp_t (fst arg)), arg) in
      let tm1 = reduce_primops cfg tm in
      let uu____4206 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps) in
      if uu____4206
      then tm1
      else
        (match tm1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.tk = uu____4209;
                     FStar_Syntax_Syntax.pos = uu____4210;
                     FStar_Syntax_Syntax.vars = uu____4211;_},uu____4212);
                FStar_Syntax_Syntax.tk = uu____4213;
                FStar_Syntax_Syntax.pos = uu____4214;
                FStar_Syntax_Syntax.vars = uu____4215;_},args)
             ->
             let uu____4235 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____4235
             then
               let uu____4236 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____4236 with
                | (Some (true ),uu____4269)::(uu____4270,(arg,uu____4272))::[]
                    -> arg
                | (uu____4313,(arg,uu____4315))::(Some (true ),uu____4316)::[]
                    -> arg
                | (Some (false ),uu____4357)::uu____4358::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4396::(Some (false ),uu____4397)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4435 -> tm1)
             else
               (let uu____4445 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____4445
                then
                  let uu____4446 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____4446 with
                  | (Some (true ),uu____4479)::uu____4480::[] ->
                      w FStar_Syntax_Util.t_true
                  | uu____4518::(Some (true ),uu____4519)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),uu____4557)::(uu____4558,(arg,uu____4560))::[]
                      -> arg
                  | (uu____4601,(arg,uu____4603))::(Some (false ),uu____4604)::[]
                      -> arg
                  | uu____4645 -> tm1
                else
                  (let uu____4655 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____4655
                   then
                     let uu____4656 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____4656 with
                     | uu____4689::(Some (true ),uu____4690)::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (false ),uu____4728)::uu____4729::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____4767)::(uu____4768,(arg,uu____4770))::[]
                         -> arg
                     | (uu____4811,(p,uu____4813))::(uu____4814,(q,uu____4816))::[]
                         ->
                         let uu____4858 = FStar_Syntax_Util.term_eq p q in
                         (if uu____4858
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____4860 -> tm1
                   else
                     (let uu____4870 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____4870
                      then
                        let uu____4871 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____4871 with
                        | (Some (true ),uu____4904)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____4928)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____4952 -> tm1
                      else
                        (let uu____4962 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid in
                         if uu____4962
                         then
                           match args with
                           | (t,uu____4964)::[] ->
                               let uu____4977 =
                                 let uu____4978 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____4978.FStar_Syntax_Syntax.n in
                               (match uu____4977 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____4981::[],body,uu____4983) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____4999 -> tm1)
                                | uu____5001 -> tm1)
                           | (uu____5002,Some (FStar_Syntax_Syntax.Implicit
                              uu____5003))::(t,uu____5005)::[] ->
                               let uu____5032 =
                                 let uu____5033 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5033.FStar_Syntax_Syntax.n in
                               (match uu____5032 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5036::[],body,uu____5038) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5054 -> tm1)
                                | uu____5056 -> tm1)
                           | uu____5057 -> tm1
                         else
                           (let uu____5064 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid in
                            if uu____5064
                            then
                              match args with
                              | (t,uu____5066)::[] ->
                                  let uu____5079 =
                                    let uu____5080 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5080.FStar_Syntax_Syntax.n in
                                  (match uu____5079 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5083::[],body,uu____5085) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5101 -> tm1)
                                   | uu____5103 -> tm1)
                              | (uu____5104,Some
                                 (FStar_Syntax_Syntax.Implicit uu____5105))::
                                  (t,uu____5107)::[] ->
                                  let uu____5134 =
                                    let uu____5135 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5135.FStar_Syntax_Syntax.n in
                                  (match uu____5134 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5138::[],body,uu____5140) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5156 -> tm1)
                                   | uu____5158 -> tm1)
                              | uu____5159 -> tm1
                            else reduce_equality cfg tm1)))))
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                FStar_Syntax_Syntax.tk = uu____5167;
                FStar_Syntax_Syntax.pos = uu____5168;
                FStar_Syntax_Syntax.vars = uu____5169;_},args)
             ->
             let uu____5185 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____5185
             then
               let uu____5186 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____5186 with
                | (Some (true ),uu____5219)::(uu____5220,(arg,uu____5222))::[]
                    -> arg
                | (uu____5263,(arg,uu____5265))::(Some (true ),uu____5266)::[]
                    -> arg
                | (Some (false ),uu____5307)::uu____5308::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____5346::(Some (false ),uu____5347)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____5385 -> tm1)
             else
               (let uu____5395 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____5395
                then
                  let uu____5396 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____5396 with
                  | (Some (true ),uu____5429)::uu____5430::[] ->
                      w FStar_Syntax_Util.t_true
                  | uu____5468::(Some (true ),uu____5469)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),uu____5507)::(uu____5508,(arg,uu____5510))::[]
                      -> arg
                  | (uu____5551,(arg,uu____5553))::(Some (false ),uu____5554)::[]
                      -> arg
                  | uu____5595 -> tm1
                else
                  (let uu____5605 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____5605
                   then
                     let uu____5606 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____5606 with
                     | uu____5639::(Some (true ),uu____5640)::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (false ),uu____5678)::uu____5679::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____5717)::(uu____5718,(arg,uu____5720))::[]
                         -> arg
                     | (uu____5761,(p,uu____5763))::(uu____5764,(q,uu____5766))::[]
                         ->
                         let uu____5808 = FStar_Syntax_Util.term_eq p q in
                         (if uu____5808
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____5810 -> tm1
                   else
                     (let uu____5820 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____5820
                      then
                        let uu____5821 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____5821 with
                        | (Some (true ),uu____5854)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____5878)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____5902 -> tm1
                      else
                        (let uu____5912 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid in
                         if uu____5912
                         then
                           match args with
                           | (t,uu____5914)::[] ->
                               let uu____5927 =
                                 let uu____5928 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5928.FStar_Syntax_Syntax.n in
                               (match uu____5927 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5931::[],body,uu____5933) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5949 -> tm1)
                                | uu____5951 -> tm1)
                           | (uu____5952,Some (FStar_Syntax_Syntax.Implicit
                              uu____5953))::(t,uu____5955)::[] ->
                               let uu____5982 =
                                 let uu____5983 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5983.FStar_Syntax_Syntax.n in
                               (match uu____5982 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5986::[],body,uu____5988) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____6004 -> tm1)
                                | uu____6006 -> tm1)
                           | uu____6007 -> tm1
                         else
                           (let uu____6014 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid in
                            if uu____6014
                            then
                              match args with
                              | (t,uu____6016)::[] ->
                                  let uu____6029 =
                                    let uu____6030 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____6030.FStar_Syntax_Syntax.n in
                                  (match uu____6029 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6033::[],body,uu____6035) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____6051 -> tm1)
                                   | uu____6053 -> tm1)
                              | (uu____6054,Some
                                 (FStar_Syntax_Syntax.Implicit uu____6055))::
                                  (t,uu____6057)::[] ->
                                  let uu____6084 =
                                    let uu____6085 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____6085.FStar_Syntax_Syntax.n in
                                  (match uu____6084 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6088::[],body,uu____6090) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____6106 -> tm1)
                                   | uu____6108 -> tm1)
                              | uu____6109 -> tm1
                            else reduce_equality cfg tm1)))))
         | uu____6116 -> tm1)
let is_norm_request hd1 args =
  let uu____6134 =
    let uu____6138 =
      let uu____6139 = FStar_Syntax_Util.un_uinst hd1 in
      uu____6139.FStar_Syntax_Syntax.n in
    (uu____6138, args) in
  match uu____6134 with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6144::uu____6145::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize_term
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6148::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize
  | uu____6150 -> false
let get_norm_request args =
  match args with
  | uu____6172::(tm,uu____6174)::[] -> tm
  | (tm,uu____6184)::[] -> tm
  | uu____6189 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___143_6197  ->
    match uu___143_6197 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.tk = uu____6199;
           FStar_Syntax_Syntax.pos = uu____6200;
           FStar_Syntax_Syntax.vars = uu____6201;_},uu____6202,uu____6203))::uu____6204
        -> true
    | uu____6210 -> false
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
            (fun uu____6324  ->
               let uu____6325 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____6326 = FStar_Syntax_Print.term_to_string t1 in
               let uu____6327 =
                 let uu____6328 =
                   let uu____6330 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives.fst uu____6330 in
                 stack_to_string uu____6328 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____6325
                 uu____6326 uu____6327);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____6342 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____6357 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____6366 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____6367 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6368;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____6369;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6374;
                 FStar_Syntax_Syntax.fv_delta = uu____6375;
                 FStar_Syntax_Syntax.fv_qual = Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6379;
                 FStar_Syntax_Syntax.fv_delta = uu____6380;
                 FStar_Syntax_Syntax.fv_qual = Some
                   (FStar_Syntax_Syntax.Record_ctor uu____6381);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (FStar_Syntax_Util.is_fstar_tactics_embed hd1) ||
                 (FStar_Syntax_Util.is_fstar_tactics_by_tactic hd1)
               ->
               let args1 = closures_as_args_delayed cfg env args in
               let hd2 = closure_as_term cfg env hd1 in
               let t2 =
                 let uu___169_6414 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.tk =
                     (uu___169_6414.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___169_6414.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___169_6414.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____6440 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____6440) && (is_norm_request hd1 args))
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
                 let uu___170_6453 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___170_6453.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___170_6453.primitive_steps)
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
                  FStar_Syntax_Syntax.tk = uu____6458;
                  FStar_Syntax_Syntax.pos = uu____6459;
                  FStar_Syntax_Syntax.vars = uu____6460;_},a1::a2::rest)
               ->
               let uu____6494 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6494 with
                | (hd1,uu____6505) ->
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
                    (FStar_Const.Const_reflect uu____6560);
                  FStar_Syntax_Syntax.tk = uu____6561;
                  FStar_Syntax_Syntax.pos = uu____6562;
                  FStar_Syntax_Syntax.vars = uu____6563;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____6586 = FStar_List.tl stack1 in
               norm cfg env uu____6586 (fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.tk = uu____6589;
                  FStar_Syntax_Syntax.pos = uu____6590;
                  FStar_Syntax_Syntax.vars = uu____6591;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____6614 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6614 with
                | (reify_head,uu____6625) ->
                    let a1 =
                      let uu____6641 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (fst a) in
                      FStar_Syntax_Subst.compress uu____6641 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____6644);
                            FStar_Syntax_Syntax.tk = uu____6645;
                            FStar_Syntax_Syntax.pos = uu____6646;
                            FStar_Syntax_Syntax.vars = uu____6647;_},a2::[])
                         -> norm cfg env stack1 (fst a2)
                     | uu____6672 ->
                         let stack2 =
                           (App
                              (reify_head, None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____6680 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____6680
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____6687 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____6687
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____6690 =
                      let uu____6694 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____6694, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____6690 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___144_6703  ->
                         match uu___144_6703 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____6706 =
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
                 if uu____6706 then false else should_delta in
               if Prims.op_Negation should_delta1
               then rebuild cfg env stack1 t1
               else
                 (let r_env =
                    let uu____6710 = FStar_Syntax_Syntax.range_of_fv f in
                    FStar_TypeChecker_Env.set_range cfg.tcenv uu____6710 in
                  let uu____6711 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  match uu____6711 with
                  | None  ->
                      (log cfg
                         (fun uu____6722  ->
                            FStar_Util.print "Tm_fvar case 2\n" []);
                       rebuild cfg env stack1 t1)
                  | Some (us,t2) ->
                      (log cfg
                         (fun uu____6728  ->
                            let uu____6729 =
                              FStar_Syntax_Print.term_to_string t0 in
                            let uu____6730 =
                              FStar_Syntax_Print.term_to_string t2 in
                            FStar_Util.print2 ">>> Unfolded %s to %s\n"
                              uu____6729 uu____6730);
                       (let t3 =
                          let uu____6732 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 (UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant)) in
                          if uu____6732
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
                          | (UnivArgs (us',uu____6748))::stack2 ->
                              let env1 =
                                FStar_All.pipe_right us'
                                  (FStar_List.fold_left
                                     (fun env1  -> fun u  -> (Univ u) :: env1)
                                     env) in
                              norm cfg env1 stack2 t3
                          | uu____6761 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack1 t3
                          | uu____6762 ->
                              let uu____6763 =
                                let uu____6764 =
                                  FStar_Syntax_Print.lid_to_string
                                    (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                FStar_Util.format1
                                  "Impossible: missing universe instantiation on %s"
                                  uu____6764 in
                              failwith uu____6763
                        else norm cfg env stack1 t3)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____6771 = lookup_bvar env x in
               (match uu____6771 with
                | Univ uu____6772 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____6787 = FStar_ST.read r in
                      (match uu____6787 with
                       | Some (env2,t') ->
                           (log cfg
                              (fun uu____6806  ->
                                 let uu____6807 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____6808 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____6807
                                   uu____6808);
                            (let uu____6809 =
                               let uu____6810 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____6810.FStar_Syntax_Syntax.n in
                             match uu____6809 with
                             | FStar_Syntax_Syntax.Tm_abs uu____6813 ->
                                 norm cfg env2 stack1 t'
                             | uu____6823 -> rebuild cfg env2 stack1 t'))
                       | None  -> norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____6846)::uu____6847 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____6852)::uu____6853 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____6859,uu____6860))::stack_rest ->
                    (match c with
                     | Univ uu____6863 -> norm cfg (c :: env) stack_rest t1
                     | uu____6864 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____6867::[] ->
                              (match lopt with
                               | None  when FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____6875  ->
                                         let uu____6876 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6876);
                                    norm cfg (c :: env) stack_rest body)
                               | Some rc when
                                   ((FStar_Ident.lid_equals
                                       rc.FStar_Syntax_Syntax.residual_effect
                                       FStar_Syntax_Const.effect_Tot_lid)
                                      ||
                                      (FStar_Ident.lid_equals
                                         rc.FStar_Syntax_Syntax.residual_effect
                                         FStar_Syntax_Const.effect_GTot_lid))
                                     ||
                                     (FStar_All.pipe_right
                                        rc.FStar_Syntax_Syntax.residual_flags
                                        (FStar_Util.for_some
                                           (fun uu___145_6879  ->
                                              match uu___145_6879 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____6880 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____6882  ->
                                         let uu____6883 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6883);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____6884 when
                                   FStar_All.pipe_right cfg.steps
                                     (FStar_List.contains Reify)
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____6886 ->
                                   let cfg1 =
                                     let uu___171_6889 = cfg in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___171_6889.tcenv);
                                       delta_level =
                                         (uu___171_6889.delta_level);
                                       primitive_steps =
                                         (uu___171_6889.primitive_steps)
                                     } in
                                   let uu____6890 =
                                     closure_as_term cfg1 env t1 in
                                   rebuild cfg1 env stack1 uu____6890)
                          | uu____6891::tl1 ->
                              (log cfg
                                 (fun uu____6901  ->
                                    let uu____6902 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____6902);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___172_6921 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___172_6921.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____6934  ->
                          let uu____6935 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____6935);
                     norm cfg env stack2 t1)
                | (Debug uu____6936)::uu____6937 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____6939 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____6939
                    else
                      (let uu____6941 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____6941 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some rc ->
                                 let uu____6952 =
                                   let uu___173_6953 = rc in
                                   let uu____6954 =
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                   {
                                     FStar_Syntax_Syntax.residual_effect =
                                       (uu___173_6953.FStar_Syntax_Syntax.residual_effect);
                                     FStar_Syntax_Syntax.residual_typ =
                                       uu____6954;
                                     FStar_Syntax_Syntax.residual_flags =
                                       (uu___173_6953.FStar_Syntax_Syntax.residual_flags)
                                   } in
                                 Some uu____6952
                             | uu____6960 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____6969  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____6974  ->
                                 let uu____6975 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____6975);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___174_6987 = cfg in
                               let uu____6988 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___174_6987.steps);
                                 tcenv = (uu___174_6987.tcenv);
                                 delta_level = (uu___174_6987.delta_level);
                                 primitive_steps = uu____6988
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____6993)::uu____6994 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____6998 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____6998
                    else
                      (let uu____7000 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7000 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some rc ->
                                 let uu____7011 =
                                   let uu___173_7012 = rc in
                                   let uu____7013 =
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                   {
                                     FStar_Syntax_Syntax.residual_effect =
                                       (uu___173_7012.FStar_Syntax_Syntax.residual_effect);
                                     FStar_Syntax_Syntax.residual_typ =
                                       uu____7013;
                                     FStar_Syntax_Syntax.residual_flags =
                                       (uu___173_7012.FStar_Syntax_Syntax.residual_flags)
                                   } in
                                 Some uu____7011
                             | uu____7019 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7028  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7033  ->
                                 let uu____7034 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7034);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___174_7046 = cfg in
                               let uu____7047 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___174_7046.steps);
                                 tcenv = (uu___174_7046.tcenv);
                                 delta_level = (uu___174_7046.delta_level);
                                 primitive_steps = uu____7047
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____7052)::uu____7053 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7059 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7059
                    else
                      (let uu____7061 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7061 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some rc ->
                                 let uu____7072 =
                                   let uu___173_7073 = rc in
                                   let uu____7074 =
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                   {
                                     FStar_Syntax_Syntax.residual_effect =
                                       (uu___173_7073.FStar_Syntax_Syntax.residual_effect);
                                     FStar_Syntax_Syntax.residual_typ =
                                       uu____7074;
                                     FStar_Syntax_Syntax.residual_flags =
                                       (uu___173_7073.FStar_Syntax_Syntax.residual_flags)
                                   } in
                                 Some uu____7072
                             | uu____7080 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7089  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7094  ->
                                 let uu____7095 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7095);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___174_7107 = cfg in
                               let uu____7108 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___174_7107.steps);
                                 tcenv = (uu___174_7107.tcenv);
                                 delta_level = (uu___174_7107.delta_level);
                                 primitive_steps = uu____7108
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____7113)::uu____7114 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7119 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7119
                    else
                      (let uu____7121 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7121 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some rc ->
                                 let uu____7132 =
                                   let uu___173_7133 = rc in
                                   let uu____7134 =
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                   {
                                     FStar_Syntax_Syntax.residual_effect =
                                       (uu___173_7133.FStar_Syntax_Syntax.residual_effect);
                                     FStar_Syntax_Syntax.residual_typ =
                                       uu____7134;
                                     FStar_Syntax_Syntax.residual_flags =
                                       (uu___173_7133.FStar_Syntax_Syntax.residual_flags)
                                   } in
                                 Some uu____7132
                             | uu____7140 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7149  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7154  ->
                                 let uu____7155 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7155);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___174_7167 = cfg in
                               let uu____7168 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___174_7167.steps);
                                 tcenv = (uu___174_7167.tcenv);
                                 delta_level = (uu___174_7167.delta_level);
                                 primitive_steps = uu____7168
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____7173)::uu____7174 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7182 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7182
                    else
                      (let uu____7184 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7184 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some rc ->
                                 let uu____7195 =
                                   let uu___173_7196 = rc in
                                   let uu____7197 =
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                   {
                                     FStar_Syntax_Syntax.residual_effect =
                                       (uu___173_7196.FStar_Syntax_Syntax.residual_effect);
                                     FStar_Syntax_Syntax.residual_typ =
                                       uu____7197;
                                     FStar_Syntax_Syntax.residual_flags =
                                       (uu___173_7196.FStar_Syntax_Syntax.residual_flags)
                                   } in
                                 Some uu____7195
                             | uu____7203 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7212  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7217  ->
                                 let uu____7218 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7218);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___174_7230 = cfg in
                               let uu____7231 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___174_7230.steps);
                                 tcenv = (uu___174_7230.tcenv);
                                 delta_level = (uu___174_7230.delta_level);
                                 primitive_steps = uu____7231
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7236 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7236
                    else
                      (let uu____7238 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7238 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some rc ->
                                 let uu____7249 =
                                   let uu___173_7250 = rc in
                                   let uu____7251 =
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                   {
                                     FStar_Syntax_Syntax.residual_effect =
                                       (uu___173_7250.FStar_Syntax_Syntax.residual_effect);
                                     FStar_Syntax_Syntax.residual_typ =
                                       uu____7251;
                                     FStar_Syntax_Syntax.residual_flags =
                                       (uu___173_7250.FStar_Syntax_Syntax.residual_flags)
                                   } in
                                 Some uu____7249
                             | uu____7257 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7266  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7271  ->
                                 let uu____7272 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7272);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___174_7284 = cfg in
                               let uu____7285 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___174_7284.steps);
                                 tcenv = (uu___174_7284.tcenv);
                                 delta_level = (uu___174_7284.delta_level);
                                 primitive_steps = uu____7285
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
                      (fun uu____7312  ->
                         fun stack2  ->
                           match uu____7312 with
                           | (a,aq) ->
                               let uu____7320 =
                                 let uu____7321 =
                                   let uu____7325 =
                                     let uu____7326 =
                                       let uu____7336 =
                                         FStar_Util.mk_ref None in
                                       (env, a, uu____7336, false) in
                                     Clos uu____7326 in
                                   (uu____7325, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____7321 in
                               uu____7320 :: stack2) args) in
               (log cfg
                  (fun uu____7358  ->
                     let uu____7359 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____7359);
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
                             ((let uu___175_7382 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___175_7382.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___175_7382.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____7383 ->
                      let uu____7386 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7386)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____7389 = FStar_Syntax_Subst.open_term [(x, None)] f in
                  match uu____7389 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____7405 =
                          let uu____7406 =
                            let uu____7411 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___176_7412 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___176_7412.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___176_7412.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____7411) in
                          FStar_Syntax_Syntax.Tm_refine uu____7406 in
                        mk uu____7405 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____7425 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____7425
               else
                 (let uu____7427 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____7427 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____7433 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  -> fun uu____7439  -> Dummy :: env1)
                               env) in
                        norm_comp cfg uu____7433 c1 in
                      let t2 =
                        let uu____7446 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____7446 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____7489)::uu____7490 -> norm cfg env stack1 t11
                | (Arg uu____7495)::uu____7496 -> norm cfg env stack1 t11
                | (App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.tk = uu____7501;
                       FStar_Syntax_Syntax.pos = uu____7502;
                       FStar_Syntax_Syntax.vars = uu____7503;_},uu____7504,uu____7505))::uu____7506
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____7512)::uu____7513 ->
                    norm cfg env stack1 t11
                | uu____7518 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____7521  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____7534 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____7534
                        | FStar_Util.Inr c ->
                            let uu____7542 = norm_comp cfg env c in
                            FStar_Util.Inr uu____7542 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____7547 =
                        mk
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (t12, (tc1, tacopt1), l))
                          t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____7547)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____7598,{
                              FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                uu____7599;
                              FStar_Syntax_Syntax.lbunivs = uu____7600;
                              FStar_Syntax_Syntax.lbtyp = uu____7601;
                              FStar_Syntax_Syntax.lbeff = uu____7602;
                              FStar_Syntax_Syntax.lbdef = uu____7603;_}::uu____7604),uu____7605)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____7631 =
                 (let uu____7632 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____7632) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____7633 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____7633))) in
               if uu____7631
               then
                 let env1 =
                   let uu____7636 =
                     let uu____7637 =
                       let uu____7647 = FStar_Util.mk_ref None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____7647,
                         false) in
                     Clos uu____7637 in
                   uu____7636 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____7671 =
                    let uu____7674 =
                      let uu____7675 =
                        let uu____7676 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____7676
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____7675] in
                    FStar_Syntax_Subst.open_term uu____7674 body in
                  match uu____7671 with
                  | (bs,body1) ->
                      let lb1 =
                        let uu___177_7682 = lb in
                        let uu____7683 =
                          let uu____7686 =
                            let uu____7687 = FStar_List.hd bs in
                            FStar_All.pipe_right uu____7687
                              FStar_Pervasives.fst in
                          FStar_All.pipe_right uu____7686
                            (fun _0_41  -> FStar_Util.Inl _0_41) in
                        let uu____7696 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____7699 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = uu____7683;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___177_7682.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____7696;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___177_7682.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____7699
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____7709  -> Dummy :: env1)
                             env) in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____7725 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____7725
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____7738 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____7760  ->
                        match uu____7760 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____7799 =
                                let uu___178_7800 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___178_7800.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___178_7800.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____7799 in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos in
                            let memo = FStar_Util.mk_ref None in
                            let rec_env1 = (Clos (env, fix_f_i, memo, true))
                              :: rec_env in
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1")))) (snd lbs)
                   (env, [], (Prims.parse_int "0")) in
               (match uu____7738 with
                | (rec_env,memos,uu____7860) ->
                    let uu____7875 =
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
                             let uu____7917 =
                               let uu____7918 =
                                 let uu____7928 = FStar_Util.mk_ref None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____7928, false) in
                               Clos uu____7918 in
                             uu____7917 :: env1) (snd lbs) env in
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
                             FStar_Syntax_Syntax.tk = uu____7966;
                             FStar_Syntax_Syntax.pos = uu____7967;
                             FStar_Syntax_Syntax.vars = uu____7968;_},uu____7969,uu____7970))::uu____7971
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____7977 -> false in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____7984 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____7984
                        then
                          let uu___179_7985 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___179_7985.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps = (uu___179_7985.primitive_steps)
                          }
                        else
                          (let uu___180_7987 = cfg in
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___180_7987.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta];
                             primitive_steps =
                               (uu___180_7987.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____7989 =
                         let uu____7990 = FStar_Syntax_Subst.compress head1 in
                         uu____7990.FStar_Syntax_Syntax.n in
                       match uu____7989 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____8004 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8004 with
                            | (uu____8005,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____8009 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____8016 =
                                         let uu____8017 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____8017.FStar_Syntax_Syntax.n in
                                       match uu____8016 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____8022,uu____8023))
                                           ->
                                           let uu____8032 =
                                             let uu____8033 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____8033.FStar_Syntax_Syntax.n in
                                           (match uu____8032 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____8038,msrc,uu____8040))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____8049 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                Some uu____8049
                                            | uu____8050 -> None)
                                       | uu____8051 -> None in
                                     let uu____8052 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____8052 with
                                      | Some e ->
                                          let lb1 =
                                            let uu___181_8056 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___181_8056.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___181_8056.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___181_8056.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Syntax_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____8057 =
                                            FStar_List.tl stack1 in
                                          let uu____8058 =
                                            let uu____8059 =
                                              let uu____8062 =
                                                let uu____8063 =
                                                  let uu____8071 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____8071) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____8063 in
                                              FStar_Syntax_Syntax.mk
                                                uu____8062 in
                                            uu____8059 None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____8057 uu____8058
                                      | None  ->
                                          let uu____8088 =
                                            let uu____8089 = is_return body in
                                            match uu____8089 with
                                            | Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____8092;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____8093;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____8094;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____8099 -> false in
                                          if uu____8088
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
                                                   = (Some t2);
                                                 FStar_Syntax_Syntax.residual_flags
                                                   = []
                                               } in
                                             let body2 =
                                               let uu____8122 =
                                                 let uu____8125 =
                                                   let uu____8126 =
                                                     let uu____8136 =
                                                       let uu____8138 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____8138] in
                                                     (uu____8136, body1,
                                                       (Some body_rc)) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____8126 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8125 in
                                               uu____8122 None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____8157 =
                                                 let uu____8158 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____8158.FStar_Syntax_Syntax.n in
                                               match uu____8157 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____8164::uu____8165::[])
                                                   ->
                                                   let uu____8171 =
                                                     let uu____8174 =
                                                       let uu____8175 =
                                                         let uu____8180 =
                                                           let uu____8182 =
                                                             let uu____8183 =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____8183 in
                                                           let uu____8184 =
                                                             let uu____8186 =
                                                               let uu____8187
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____8187 in
                                                             [uu____8186] in
                                                           uu____8182 ::
                                                             uu____8184 in
                                                         (bind1, uu____8180) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____8175 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8174 in
                                                   uu____8171 None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____8199 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____8205 =
                                                 let uu____8208 =
                                                   let uu____8209 =
                                                     let uu____8219 =
                                                       let uu____8221 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____8222 =
                                                         let uu____8224 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____8225 =
                                                           let uu____8227 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____8228 =
                                                             let uu____8230 =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____8231 =
                                                               let uu____8233
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____8234
                                                                 =
                                                                 let uu____8236
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____8236] in
                                                               uu____8233 ::
                                                                 uu____8234 in
                                                             uu____8230 ::
                                                               uu____8231 in
                                                           uu____8227 ::
                                                             uu____8228 in
                                                         uu____8224 ::
                                                           uu____8225 in
                                                       uu____8221 ::
                                                         uu____8222 in
                                                     (bind_inst, uu____8219) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____8209 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8208 in
                                               uu____8205 None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____8248 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____8248 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____8266 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8266 with
                            | (uu____8267,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____8290 =
                                        let uu____8291 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____8291.FStar_Syntax_Syntax.n in
                                      match uu____8290 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____8297) -> t4
                                      | uu____8302 -> head2 in
                                    let uu____8303 =
                                      let uu____8304 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____8304.FStar_Syntax_Syntax.n in
                                    match uu____8303 with
                                    | FStar_Syntax_Syntax.Tm_fvar x -> Some x
                                    | uu____8309 -> None in
                                  let uu____8310 = maybe_extract_fv head2 in
                                  match uu____8310 with
                                  | Some x when
                                      let uu____8316 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____8316
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____8320 =
                                          maybe_extract_fv head3 in
                                        match uu____8320 with
                                        | Some uu____8323 -> Some true
                                        | uu____8324 -> Some false in
                                      (head3, action_unfolded)
                                  | uu____8327 -> (head2, None) in
                                ((let is_arg_impure uu____8338 =
                                    match uu____8338 with
                                    | (e,q) ->
                                        let uu____8343 =
                                          let uu____8344 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____8344.FStar_Syntax_Syntax.n in
                                        (match uu____8343 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____8359 -> false) in
                                  let uu____8360 =
                                    let uu____8361 =
                                      let uu____8365 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____8365 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____8361 in
                                  if uu____8360
                                  then
                                    let uu____8368 =
                                      let uu____8369 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____8369 in
                                    failwith uu____8368
                                  else ());
                                 (let uu____8371 =
                                    maybe_unfold_action head_app in
                                  match uu____8371 with
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
                                      let uu____8406 = FStar_List.tl stack1 in
                                      norm cfg env uu____8406 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____8420 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____8420 in
                           let uu____8421 = FStar_List.tl stack1 in
                           norm cfg env uu____8421 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____8504  ->
                                     match uu____8504 with
                                     | (pat,wopt,tm) ->
                                         let uu____8542 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____8542))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____8568 = FStar_List.tl stack1 in
                           norm cfg env uu____8568 tm
                       | uu____8569 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.tk = uu____8578;
                             FStar_Syntax_Syntax.pos = uu____8579;
                             FStar_Syntax_Syntax.vars = uu____8580;_},uu____8581,uu____8582))::uu____8583
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____8589 -> false in
                    if should_reify
                    then
                      let uu____8590 = FStar_List.tl stack1 in
                      let uu____8591 =
                        let uu____8592 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____8592 in
                      norm cfg env uu____8590 uu____8591
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____8595 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____8595
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___182_8601 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___182_8601.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___182_8601.primitive_steps)
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
                | uu____8603 ->
                    (match stack1 with
                     | uu____8604::uu____8605 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____8609)
                              -> norm cfg env ((Meta (m, r)) :: stack1) head1
                          | FStar_Syntax_Syntax.Meta_pattern args ->
                              let args1 = norm_pattern_args cfg env args in
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_pattern args1),
                                      (t1.FStar_Syntax_Syntax.pos))) ::
                                stack1) head1
                          | uu____8624 -> norm cfg env stack1 head1)
                     | [] ->
                         let head2 = norm cfg env [] head1 in
                         let m1 =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               let uu____8634 =
                                 norm_pattern_args cfg env args in
                               FStar_Syntax_Syntax.Meta_pattern uu____8634
                           | uu____8641 -> m in
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
              let uu____8653 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____8653 with
              | (uu____8654,return_repr) ->
                  let return_inst =
                    let uu____8661 =
                      let uu____8662 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____8662.FStar_Syntax_Syntax.n in
                    match uu____8661 with
                    | FStar_Syntax_Syntax.Tm_uinst (return_tm,uu____8668::[])
                        ->
                        let uu____8674 =
                          let uu____8677 =
                            let uu____8678 =
                              let uu____8683 =
                                let uu____8685 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____8685] in
                              (return_tm, uu____8683) in
                            FStar_Syntax_Syntax.Tm_uinst uu____8678 in
                          FStar_Syntax_Syntax.mk uu____8677 in
                        uu____8674 None e.FStar_Syntax_Syntax.pos
                    | uu____8697 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____8700 =
                    let uu____8703 =
                      let uu____8704 =
                        let uu____8714 =
                          let uu____8716 = FStar_Syntax_Syntax.as_arg t in
                          let uu____8717 =
                            let uu____8719 = FStar_Syntax_Syntax.as_arg e in
                            [uu____8719] in
                          uu____8716 :: uu____8717 in
                        (return_inst, uu____8714) in
                      FStar_Syntax_Syntax.Tm_app uu____8704 in
                    FStar_Syntax_Syntax.mk uu____8703 in
                  uu____8700 None e.FStar_Syntax_Syntax.pos
            else
              (let uu____8732 = FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____8732 with
               | None  ->
                   let uu____8734 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____8734
               | Some
                   { FStar_TypeChecker_Env.msource = uu____8735;
                     FStar_TypeChecker_Env.mtarget = uu____8736;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____8737;
                         FStar_TypeChecker_Env.mlift_term = None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | Some
                   { FStar_TypeChecker_Env.msource = uu____8748;
                     FStar_TypeChecker_Env.mtarget = uu____8749;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____8750;
                         FStar_TypeChecker_Env.mlift_term = Some lift;_};_}
                   ->
                   let uu____8768 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____8768)
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
                (fun uu____8798  ->
                   match uu____8798 with
                   | (a,imp) ->
                       let uu____8805 = norm cfg env [] a in
                       (uu____8805, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___183_8820 = comp1 in
            let uu____8823 =
              let uu____8824 =
                let uu____8830 = norm cfg env [] t in
                let uu____8831 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____8830, uu____8831) in
              FStar_Syntax_Syntax.Total uu____8824 in
            {
              FStar_Syntax_Syntax.n = uu____8823;
              FStar_Syntax_Syntax.tk = (uu___183_8820.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___183_8820.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___183_8820.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___184_8846 = comp1 in
            let uu____8849 =
              let uu____8850 =
                let uu____8856 = norm cfg env [] t in
                let uu____8857 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____8856, uu____8857) in
              FStar_Syntax_Syntax.GTotal uu____8850 in
            {
              FStar_Syntax_Syntax.n = uu____8849;
              FStar_Syntax_Syntax.tk = (uu___184_8846.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___184_8846.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___184_8846.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____8888  ->
                      match uu____8888 with
                      | (a,i) ->
                          let uu____8895 = norm cfg env [] a in
                          (uu____8895, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___146_8900  ->
                      match uu___146_8900 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____8904 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____8904
                      | f -> f)) in
            let uu___185_8908 = comp1 in
            let uu____8911 =
              let uu____8912 =
                let uu___186_8913 = ct in
                let uu____8914 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____8915 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____8918 = norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____8914;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___186_8913.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____8915;
                  FStar_Syntax_Syntax.effect_args = uu____8918;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____8912 in
            {
              FStar_Syntax_Syntax.n = uu____8911;
              FStar_Syntax_Syntax.tk = (uu___185_8908.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___185_8908.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___185_8908.FStar_Syntax_Syntax.vars)
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
            (let uu___187_8935 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___187_8935.tcenv);
               delta_level = (uu___187_8935.delta_level);
               primitive_steps = (uu___187_8935.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____8940 = norm1 t in
          FStar_Syntax_Util.non_informative uu____8940 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____8943 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___188_8957 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.tk = (uu___188_8957.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___188_8957.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___188_8957.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____8967 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____8967
            then
              let ct1 =
                match downgrade_ghost_effect_name
                        ct.FStar_Syntax_Syntax.effect_name
                with
                | Some pure_eff ->
                    let uu___189_8972 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___189_8972.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___189_8972.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___189_8972.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___189_8972.FStar_Syntax_Syntax.flags)
                    }
                | None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___190_8974 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___190_8974.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Syntax_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___190_8974.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___190_8974.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___190_8974.FStar_Syntax_Syntax.flags)
                    } in
              let uu___191_8975 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.tk =
                  (uu___191_8975.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___191_8975.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___191_8975.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____8981 -> c
and norm_binder:
  cfg ->
    env ->
      FStar_Syntax_Syntax.binder ->
        (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  =
  fun cfg  ->
    fun env  ->
      fun uu____8984  ->
        match uu____8984 with
        | (x,imp) ->
            let uu____8987 =
              let uu___192_8988 = x in
              let uu____8989 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___192_8988.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___192_8988.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____8989
              } in
            (uu____8987, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____8995 =
          FStar_List.fold_left
            (fun uu____9002  ->
               fun b  ->
                 match uu____9002 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____8995 with | (nbs,uu____9019) -> FStar_List.rev nbs
and norm_lcomp_opt:
  cfg ->
    env ->
      FStar_Syntax_Syntax.residual_comp option ->
        FStar_Syntax_Syntax.residual_comp option
  =
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | Some rc ->
            let flags =
              filter_out_lcomp_cflags rc.FStar_Syntax_Syntax.residual_flags in
            let uu____9030 =
              let uu___193_9031 = rc in
              let uu____9032 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___193_9031.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____9032;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___193_9031.FStar_Syntax_Syntax.residual_flags)
              } in
            Some uu____9030
        | uu____9038 -> lopt
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
              ((let uu____9048 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____9048
                then
                  let uu____9049 = FStar_Syntax_Print.term_to_string tm in
                  let uu____9050 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2 "Normalized %s to %s\n" uu____9049
                    uu____9050
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___194_9061 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___194_9061.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____9081  ->
                    let uu____9082 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____9082);
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
              let uu____9113 =
                let uu___195_9114 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___195_9114.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___195_9114.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___195_9114.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____9113
          | (Arg (Univ uu____9119,uu____9120,uu____9121))::uu____9122 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____9124,uu____9125))::uu____9126 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____9138),aq,r))::stack2 ->
              (log cfg
                 (fun uu____9154  ->
                    let uu____9155 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____9155);
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
                 (let uu____9166 = FStar_ST.read m in
                  match uu____9166 with
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
                  | Some (uu____9192,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq) None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.extend_app head1 (t, aq) None r in
              let uu____9214 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____9214
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____9221  ->
                    let uu____9222 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____9222);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____9227 =
                  log cfg
                    (fun uu____9229  ->
                       let uu____9230 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____9231 =
                         let uu____9232 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____9239  ->
                                   match uu____9239 with
                                   | (p,uu____9245,uu____9246) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____9232
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____9230 uu____9231);
                  (let whnf = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___147_9256  ->
                               match uu___147_9256 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____9257 -> false)) in
                     let steps' =
                       let uu____9260 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____9260
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___196_9263 = cfg in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___196_9263.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___196_9263.primitive_steps)
                     } in
                   let norm_or_whnf env2 t1 =
                     if whnf
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____9297 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____9313 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____9347  ->
                                   fun uu____9348  ->
                                     match (uu____9347, uu____9348) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____9413 = norm_pat env3 p1 in
                                         (match uu____9413 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____9313 with
                          | (pats1,env3) ->
                              ((let uu___197_9479 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___197_9479.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___197_9479.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___198_9493 = x in
                           let uu____9494 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___198_9493.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___198_9493.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9494
                           } in
                         ((let uu___199_9500 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___199_9500.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___199_9500.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___200_9505 = x in
                           let uu____9506 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___200_9505.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___200_9505.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9506
                           } in
                         ((let uu___201_9512 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___201_9512.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___201_9512.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___202_9522 = x in
                           let uu____9523 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___202_9522.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___202_9522.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9523
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___203_9530 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.ty =
                               (uu___203_9530.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___203_9530.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf -> branches
                     | uu____9534 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____9537 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____9537 with
                                 | (p,wopt,e) ->
                                     let uu____9555 = norm_pat env1 p in
                                     (match uu____9555 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | None  -> None
                                            | Some w ->
                                                let uu____9579 =
                                                  norm_or_whnf env2 w in
                                                Some uu____9579 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____9584 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____9584) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____9594) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____9599 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____9600;
                        FStar_Syntax_Syntax.fv_delta = uu____9601;
                        FStar_Syntax_Syntax.fv_qual = Some
                          (FStar_Syntax_Syntax.Data_ctor );_}
                      -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____9605;
                        FStar_Syntax_Syntax.fv_delta = uu____9606;
                        FStar_Syntax_Syntax.fv_qual = Some
                          (FStar_Syntax_Syntax.Record_ctor uu____9607);_}
                      -> true
                  | uu____9614 -> false in
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
                  let uu____9713 = FStar_Syntax_Util.head_and_args scrutinee1 in
                  match uu____9713 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var uu____9745 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_wild uu____9747 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____9749 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee1.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____9761 ->
                                let uu____9762 =
                                  let uu____9763 = is_cons head1 in
                                  Prims.op_Negation uu____9763 in
                                FStar_Util.Inr uu____9762)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____9777 =
                             let uu____9778 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____9778.FStar_Syntax_Syntax.n in
                           (match uu____9777 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____9785 ->
                                let uu____9786 =
                                  let uu____9787 = is_cons head1 in
                                  Prims.op_Negation uu____9787 in
                                FStar_Util.Inr uu____9786))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____9821)::rest_a,(p1,uu____9824)::rest_p) ->
                      let uu____9852 = matches_pat t1 p1 in
                      (match uu____9852 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____9866 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____9937 = matches_pat scrutinee1 p1 in
                      (match uu____9937 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____9947  ->
                                 let uu____9948 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____9949 =
                                   let uu____9950 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____9950
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____9948 uu____9949);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____9959 =
                                        let uu____9960 =
                                          let uu____9970 =
                                            FStar_Util.mk_ref (Some ([], t1)) in
                                          ([], t1, uu____9970, false) in
                                        Clos uu____9960 in
                                      uu____9959 :: env2) env1 s in
                             let uu____9993 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____9993))) in
                let uu____9994 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____9994
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___148_10010  ->
                match uu___148_10010 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____10013 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____10017 -> d in
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
            let uu___204_10041 = config s e in
            {
              steps = (uu___204_10041.steps);
              tcenv = (uu___204_10041.tcenv);
              delta_level = (uu___204_10041.delta_level);
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
      fun t  -> let uu____10066 = config s e in norm_comp uu____10066 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____10075 = config [] env in norm_universe uu____10075 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun c  ->
      let uu____10084 = config [] env in ghost_to_pure_aux uu____10084 [] c
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
        let uu____10098 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____10098 in
      let uu____10099 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____10099
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | Some pure_eff ->
            let uu___205_10101 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___205_10101.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___205_10101.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____10102  ->
                    let uu____10103 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____10103))
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
            ((let uu____10118 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10118);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____10129 = config [AllowUnboundUniverses] env in
          norm_comp uu____10129 [] c
        with
        | e ->
            ((let uu____10133 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10133);
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
                   let uu____10173 =
                     let uu____10174 =
                       let uu____10179 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____10179) in
                     FStar_Syntax_Syntax.Tm_refine uu____10174 in
                   mk uu____10173 t01.FStar_Syntax_Syntax.pos
               | uu____10184 -> t2)
          | uu____10185 -> t2 in
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
        let uu____10214 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____10214 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____10230 ->
                 let uu____10234 = FStar_Syntax_Util.abs_formals e in
                 (match uu____10234 with
                  | (actuals,uu____10240,uu____10241) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____10257 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____10257 with
                         | (binders,args) ->
                             let uu____10267 =
                               FStar_Syntax_Syntax.mk_Tm_app e args None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____10267
                               (Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c)))))
let eta_expand:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____10278 =
        let uu____10282 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
        (uu____10282, (t.FStar_Syntax_Syntax.n)) in
      match uu____10278 with
      | (Some sort,uu____10289) ->
          let uu____10291 = mk sort t.FStar_Syntax_Syntax.pos in
          eta_expand_with_type env t uu____10291
      | (uu____10292,FStar_Syntax_Syntax.Tm_name x) ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____10296 ->
          let uu____10300 = FStar_Syntax_Util.head_and_args t in
          (match uu____10300 with
           | (head1,args) ->
               let uu____10326 =
                 let uu____10327 = FStar_Syntax_Subst.compress head1 in
                 uu____10327.FStar_Syntax_Syntax.n in
               (match uu____10326 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____10330,thead) ->
                    let uu____10344 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____10344 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____10379 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___210_10383 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___210_10383.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___210_10383.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___210_10383.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___210_10383.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___210_10383.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___210_10383.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ = None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___210_10383.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___210_10383.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___210_10383.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___210_10383.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___210_10383.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___210_10383.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___210_10383.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___210_10383.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___210_10383.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___210_10383.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___210_10383.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___210_10383.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___210_10383.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___210_10383.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___210_10383.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___210_10383.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___210_10383.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___210_10383.FStar_TypeChecker_Env.is_native_tactic)
                                 }) t in
                            match uu____10379 with
                            | (uu____10384,ty,uu____10386) ->
                                eta_expand_with_type env t ty))
                | uu____10387 ->
                    let uu____10388 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___211_10392 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___211_10392.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___211_10392.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___211_10392.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___211_10392.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___211_10392.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___211_10392.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ = None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___211_10392.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___211_10392.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___211_10392.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___211_10392.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___211_10392.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___211_10392.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___211_10392.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___211_10392.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___211_10392.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___211_10392.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___211_10392.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___211_10392.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___211_10392.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___211_10392.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___211_10392.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___211_10392.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___211_10392.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___211_10392.FStar_TypeChecker_Env.is_native_tactic)
                         }) t in
                    (match uu____10388 with
                     | (uu____10393,ty,uu____10395) ->
                         eta_expand_with_type env t ty)))