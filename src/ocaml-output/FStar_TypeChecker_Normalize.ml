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
      FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term option;}
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
  fun uu___130_219  ->
    match uu___130_219 with
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
      FStar_Util.either option* FStar_Range.range)
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
  fun uu___131_658  ->
    match uu___131_658 with
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
let is_empty uu___132_739 =
  match uu___132_739 with | [] -> true | uu____741 -> false
let lookup_bvar env x =
  try FStar_List.nth env x.FStar_Syntax_Syntax.index
  with
  | uu____759 ->
      let uu____760 =
        let uu____761 = FStar_Syntax_Print.db_to_string x in
        FStar_Util.format1 "Failed to find %s\n" uu____761 in
      failwith uu____760
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
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____863 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____866 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____871 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____871 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____882 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____882 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____887 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____890 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____890 with
                                  | (uu____893,m) -> n1 <= m)) in
                        if uu____887 then rest1 else us1
                    | uu____897 -> us1)
               | uu____900 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____903 = aux u3 in
              FStar_List.map (fun _0_30  -> FStar_Syntax_Syntax.U_succ _0_30)
                uu____903 in
        let uu____905 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____905
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____907 = aux u in
           match uu____907 with
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
          (fun uu____1004  ->
             let uu____1005 = FStar_Syntax_Print.tag_of_term t in
             let uu____1006 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1005
               uu____1006);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1007 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1010 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____1031 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____1032 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____1033 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____1034 -> t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____1044 =
                    let uu____1045 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____1045 in
                  mk uu____1044 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t2,us) ->
                  let uu____1052 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t2 uu____1052
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____1054 = lookup_bvar env x in
                  (match uu____1054 with
                   | Univ uu____1055 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____1059) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____1127 = closures_as_binders_delayed cfg env bs in
                  (match uu____1127 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____1147 =
                         let uu____1148 =
                           let uu____1163 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____1163) in
                         FStar_Syntax_Syntax.Tm_abs uu____1148 in
                       mk uu____1147 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____1193 = closures_as_binders_delayed cfg env bs in
                  (match uu____1193 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____1224 =
                    let uu____1231 =
                      let uu____1235 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____1235] in
                    closures_as_binders_delayed cfg env uu____1231 in
                  (match uu____1224 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____1249 =
                         let uu____1250 =
                           let uu____1255 =
                             let uu____1256 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____1256
                               FStar_Pervasives.fst in
                           (uu____1255, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____1250 in
                       mk uu____1249 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____1324 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____1324
                    | FStar_Util.Inr c ->
                        let uu____1338 = close_comp cfg env c in
                        FStar_Util.Inr uu____1338 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____1353 =
                    let uu____1354 =
                      let uu____1372 = closure_as_term_delayed cfg env t11 in
                      (uu____1372, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____1354 in
                  mk uu____1353 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____1410 =
                    let uu____1411 =
                      let uu____1416 = closure_as_term_delayed cfg env t' in
                      let uu____1419 =
                        let uu____1420 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____1420 in
                      (uu____1416, uu____1419) in
                    FStar_Syntax_Syntax.Tm_meta uu____1411 in
                  mk uu____1410 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____1462 =
                    let uu____1463 =
                      let uu____1468 = closure_as_term_delayed cfg env t' in
                      let uu____1471 =
                        let uu____1472 =
                          let uu____1477 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____1477) in
                        FStar_Syntax_Syntax.Meta_monadic uu____1472 in
                      (uu____1468, uu____1471) in
                    FStar_Syntax_Syntax.Tm_meta uu____1463 in
                  mk uu____1462 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____1496 =
                    let uu____1497 =
                      let uu____1502 = closure_as_term_delayed cfg env t' in
                      let uu____1505 =
                        let uu____1506 =
                          let uu____1512 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____1512) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____1506 in
                      (uu____1502, uu____1505) in
                    FStar_Syntax_Syntax.Tm_meta uu____1497 in
                  mk uu____1496 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____1525 =
                    let uu____1526 =
                      let uu____1531 = closure_as_term_delayed cfg env t' in
                      (uu____1531, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____1526 in
                  mk uu____1525 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____1552  -> Dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let body1 =
                    match lb.FStar_Syntax_Syntax.lbname with
                    | FStar_Util.Inr uu____1563 -> body
                    | FStar_Util.Inl uu____1564 ->
                        closure_as_term cfg (Dummy :: env0) body in
                  let lb1 =
                    let uu___145_1566 = lb in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___145_1566.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___145_1566.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = typ;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___145_1566.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = def
                    } in
                  mk (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((uu____1573,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____1597  -> fun env2  -> Dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____1602 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____1602
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____1606  -> fun env2  -> Dummy :: env2) lbs
                          env_univs in
                    let uu___146_1609 = lb in
                    let uu____1610 =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let uu____1613 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___146_1609.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___146_1609.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = uu____1610;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___146_1609.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____1613
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____1624  -> fun env1  -> Dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____1679 =
                    match uu____1679 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____1725 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_disj [] ->
                              failwith "Impossible"
                          | FStar_Syntax_Syntax.Pat_disj (hd1::tl1) ->
                              let uu____1745 = norm_pat env2 hd1 in
                              (match uu____1745 with
                               | (hd2,env') ->
                                   let tl2 =
                                     FStar_All.pipe_right tl1
                                       (FStar_List.map
                                          (fun p1  ->
                                             let uu____1781 =
                                               norm_pat env2 p1 in
                                             fst uu____1781)) in
                                   ((let uu___147_1793 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_disj (hd2
                                            :: tl2));
                                       FStar_Syntax_Syntax.ty =
                                         (uu___147_1793.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___147_1793.FStar_Syntax_Syntax.p)
                                     }), env'))
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____1810 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____1844  ->
                                        fun uu____1845  ->
                                          match (uu____1844, uu____1845) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____1910 =
                                                norm_pat env3 p1 in
                                              (match uu____1910 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____1810 with
                               | (pats1,env3) ->
                                   ((let uu___148_1976 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.ty =
                                         (uu___148_1976.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___148_1976.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___149_1990 = x in
                                let uu____1991 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___149_1990.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___149_1990.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1991
                                } in
                              ((let uu___150_1997 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___150_1997.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___150_1997.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___151_2002 = x in
                                let uu____2003 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___151_2002.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___151_2002.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____2003
                                } in
                              ((let uu___152_2009 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___152_2009.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___152_2009.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___153_2019 = x in
                                let uu____2020 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___153_2019.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___153_2019.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____2020
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___154_2027 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___154_2027.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___154_2027.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____2030 = norm_pat env1 pat in
                        (match uu____2030 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | None  -> None
                               | Some w ->
                                   let uu____2054 =
                                     closure_as_term cfg env2 w in
                                   Some uu____2054 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____2059 =
                    let uu____2060 =
                      let uu____2076 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____2076) in
                    FStar_Syntax_Syntax.Tm_match uu____2060 in
                  mk uu____2059 t1.FStar_Syntax_Syntax.pos))
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
        | uu____2129 -> closure_as_term cfg env t
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
        | uu____2145 ->
            FStar_List.map
              (fun uu____2155  ->
                 match uu____2155 with
                 | (x,imp) ->
                     let uu____2170 = closure_as_term_delayed cfg env x in
                     (uu____2170, imp)) args
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
        let uu____2182 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____2206  ->
                  fun uu____2207  ->
                    match (uu____2206, uu____2207) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___155_2251 = b in
                          let uu____2252 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___155_2251.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___155_2251.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____2252
                          } in
                        let env2 = Dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____2182 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____2299 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____2311 = closure_as_term_delayed cfg env t in
                 let uu____2312 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____2311 uu____2312
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____2322 = closure_as_term_delayed cfg env t in
                 let uu____2323 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____2322 uu____2323
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
                        (fun uu___133_2339  ->
                           match uu___133_2339 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____2343 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____2343
                           | f -> f)) in
                 let uu____2347 =
                   let uu___156_2348 = c1 in
                   let uu____2349 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____2349;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___156_2348.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____2347)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.cflags Prims.list =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_List.filter
         (fun uu___134_2353  ->
            match uu___134_2353 with
            | FStar_Syntax_Syntax.DECREASES uu____2354 -> false
            | uu____2357 -> true))
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
            let uu____2385 = FStar_Syntax_Util.is_total_lcomp lc in
            if uu____2385
            then
              Some
                (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, flags))
            else
              (let uu____2402 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
               if uu____2402
               then
                 Some
                   (FStar_Util.Inr
                      (FStar_Syntax_Const.effect_GTot_lid, flags))
               else
                 Some
                   (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags)))
        | uu____2428 -> lopt
let built_in_primitive_steps: primitive_step Prims.list =
  let const_as_tm c p = mk (FStar_Syntax_Syntax.Tm_constant c) p in
  let int_as_const p i =
    let uu____2452 =
      let uu____2453 =
        let uu____2459 = FStar_Util.string_of_int i in (uu____2459, None) in
      FStar_Const.Const_int uu____2453 in
    const_as_tm uu____2452 p in
  let bool_as_const p b = const_as_tm (FStar_Const.Const_bool b) p in
  let string_as_const p b =
    const_as_tm
      (FStar_Const.Const_string ((FStar_Util.bytes_of_string b), p)) p in
  let arg_as_int uu____2486 =
    match uu____2486 with
    | (a,uu____2491) ->
        let uu____2493 =
          let uu____2494 = FStar_Syntax_Subst.compress a in
          uu____2494.FStar_Syntax_Syntax.n in
        (match uu____2493 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i,None ))
             ->
             let uu____2504 = FStar_Util.int_of_string i in Some uu____2504
         | uu____2505 -> None) in
  let arg_as_bounded_int uu____2514 =
    match uu____2514 with
    | (a,uu____2521) ->
        let uu____2525 =
          let uu____2526 = FStar_Syntax_Subst.compress a in
          uu____2526.FStar_Syntax_Syntax.n in
        (match uu____2525 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.tk = uu____2533;
                FStar_Syntax_Syntax.pos = uu____2534;
                FStar_Syntax_Syntax.vars = uu____2535;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,None ));
                                                            FStar_Syntax_Syntax.tk
                                                              = uu____2537;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____2538;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____2539;_},uu____2540)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____2571 =
               let uu____2574 = FStar_Util.int_of_string i in
               (fv1, uu____2574) in
             Some uu____2571
         | uu____2577 -> None) in
  let arg_as_bool uu____2586 =
    match uu____2586 with
    | (a,uu____2591) ->
        let uu____2593 =
          let uu____2594 = FStar_Syntax_Subst.compress a in
          uu____2594.FStar_Syntax_Syntax.n in
        (match uu____2593 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
             Some b
         | uu____2599 -> None) in
  let arg_as_char uu____2606 =
    match uu____2606 with
    | (a,uu____2611) ->
        let uu____2613 =
          let uu____2614 = FStar_Syntax_Subst.compress a in
          uu____2614.FStar_Syntax_Syntax.n in
        (match uu____2613 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
             Some c
         | uu____2619 -> None) in
  let arg_as_string uu____2626 =
    match uu____2626 with
    | (a,uu____2631) ->
        let uu____2633 =
          let uu____2634 = FStar_Syntax_Subst.compress a in
          uu____2634.FStar_Syntax_Syntax.n in
        (match uu____2633 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (bytes,uu____2639)) -> Some (FStar_Util.string_of_bytes bytes)
         | uu____2642 -> None) in
  let arg_as_list f uu____2663 =
    match uu____2663 with
    | (a,uu____2672) ->
        let rec sequence l =
          match l with
          | [] -> Some []
          | (None )::uu____2691 -> None
          | (Some x)::xs ->
              let uu____2701 = sequence xs in
              (match uu____2701 with
               | None  -> None
               | Some xs' -> Some (x :: xs')) in
        let uu____2712 = FStar_Syntax_Util.list_elements a in
        (match uu____2712 with
         | None  -> None
         | Some elts ->
             let uu____2722 =
               FStar_List.map
                 (fun x  ->
                    let uu____2727 = FStar_Syntax_Syntax.as_arg x in
                    f uu____2727) elts in
             sequence uu____2722) in
  let lift_unary f aopts =
    match aopts with
    | (Some a)::[] -> let uu____2757 = f a in Some uu____2757
    | uu____2758 -> None in
  let lift_binary f aopts =
    match aopts with
    | (Some a0)::(Some a1)::[] -> let uu____2797 = f a0 a1 in Some uu____2797
    | uu____2798 -> None in
  let unary_op as_a f r args =
    let uu____2842 = FStar_List.map as_a args in lift_unary (f r) uu____2842 in
  let binary_op as_a f r args =
    let uu____2892 = FStar_List.map as_a args in lift_binary (f r) uu____2892 in
  let as_primitive_step uu____2909 =
    match uu____2909 with
    | (l,arity,f) ->
        { name = l; arity; strong_reduction_ok = true; interpretation = f } in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  -> fun x  -> let uu____2947 = f x in int_as_const r uu____2947) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2970 = f x y in int_as_const r uu____2970) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  -> fun x  -> let uu____2987 = f x in bool_as_const r uu____2987) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  -> let uu____3010 = f x y in bool_as_const r uu____3010) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  -> let uu____3033 = f x y in string_as_const r uu____3033) in
  let list_of_string' rng s =
    let name l =
      let uu____3047 =
        let uu____3048 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            None in
        FStar_Syntax_Syntax.Tm_fvar uu____3048 in
      mk uu____3047 rng in
    let char_t = name FStar_Syntax_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____3058 =
      let uu____3060 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____3060 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____3058 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Const.exp_string s in
  let string_of_int1 rng i =
    let uu____3082 = FStar_Util.string_of_int i in
    string_as_const rng uu____3082 in
  let string_of_bool1 rng b =
    string_as_const rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____3098 = FStar_Util.string_of_int i in
    string_as_const rng uu____3098 in
  let string_of_bool2 rng b =
    string_as_const rng (if b then "true" else "false") in
  let basic_ops =
    let uu____3117 =
      let uu____3127 =
        let uu____3137 =
          let uu____3147 =
            let uu____3157 =
              let uu____3167 =
                let uu____3177 =
                  let uu____3187 =
                    let uu____3197 =
                      let uu____3207 =
                        let uu____3217 =
                          let uu____3227 =
                            let uu____3237 =
                              let uu____3247 =
                                let uu____3257 =
                                  let uu____3267 =
                                    let uu____3277 =
                                      let uu____3286 =
                                        FStar_Syntax_Const.p2l
                                          ["FStar";
                                          "String";
                                          "list_of_string"] in
                                      (uu____3286, (Prims.parse_int "1"),
                                        (unary_op arg_as_string
                                           list_of_string')) in
                                    let uu____3292 =
                                      let uu____3302 =
                                        let uu____3311 =
                                          FStar_Syntax_Const.p2l
                                            ["FStar";
                                            "String";
                                            "string_of_list"] in
                                        (uu____3311, (Prims.parse_int "1"),
                                          (unary_op (arg_as_list arg_as_char)
                                             string_of_list')) in
                                      [uu____3302] in
                                    uu____3277 :: uu____3292 in
                                  (FStar_Syntax_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_bool string_of_bool2))
                                    :: uu____3267 in
                                (FStar_Syntax_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (unary_op arg_as_int string_of_int2)) ::
                                  uu____3257 in
                              (FStar_Syntax_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____3247 in
                            (FStar_Syntax_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____3237 in
                          (FStar_Syntax_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____3227 in
                        (FStar_Syntax_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____3217 in
                      (FStar_Syntax_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____3207 in
                    (FStar_Syntax_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
                      :: uu____3197 in
                  (FStar_Syntax_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____3187 in
                (FStar_Syntax_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____3177 in
              (FStar_Syntax_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____3167 in
            (FStar_Syntax_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____3157 in
          (FStar_Syntax_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____3147 in
        (FStar_Syntax_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____3137 in
      (FStar_Syntax_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____3127 in
    (FStar_Syntax_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____3117 in
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
      let uu____3606 =
        let uu____3607 =
          let uu____3608 = FStar_Syntax_Syntax.as_arg c in [uu____3608] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____3607 in
      uu____3606 None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____3632 =
              let uu____3641 = FStar_Syntax_Const.p2l ["FStar"; m; "add"] in
              (uu____3641, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____3650  ->
                        fun uu____3651  ->
                          match (uu____3650, uu____3651) with
                          | ((int_to_t1,x),(uu____3662,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____3668 =
              let uu____3678 =
                let uu____3687 = FStar_Syntax_Const.p2l ["FStar"; m; "sub"] in
                (uu____3687, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____3696  ->
                          fun uu____3697  ->
                            match (uu____3696, uu____3697) with
                            | ((int_to_t1,x),(uu____3708,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____3714 =
                let uu____3724 =
                  let uu____3733 = FStar_Syntax_Const.p2l ["FStar"; m; "mul"] in
                  (uu____3733, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____3742  ->
                            fun uu____3743  ->
                              match (uu____3742, uu____3743) with
                              | ((int_to_t1,x),(uu____3754,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____3724] in
              uu____3678 :: uu____3714 in
            uu____3632 :: uu____3668)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_bool rng args =
    match args with
    | (_typ,uu____3820)::(a1,uu____3822)::(a2,uu____3824)::[] ->
        let uu____3853 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3853 with
         | FStar_Syntax_Util.Equal  ->
             let uu____3855 =
               mk
                 (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_bool true)) rng in
             Some uu____3855
         | FStar_Syntax_Util.NotEqual  ->
             let uu____3860 =
               mk
                 (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_bool false)) rng in
             Some uu____3860
         | uu____3865 -> None)
    | uu____3866 -> failwith "Unexpected number of arguments" in
  let interp_prop r args =
    match args with
    | (_typ,uu____3879)::(a1,uu____3881)::(a2,uu____3883)::[] ->
        let uu____3912 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3912 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___157_3916 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___157_3916.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___157_3916.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___157_3916.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___158_3923 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___158_3923.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___158_3923.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___158_3923.FStar_Syntax_Syntax.vars)
                })
         | uu____3928 -> None)
    | (_typ,uu____3930)::uu____3931::(a1,uu____3933)::(a2,uu____3935)::[] ->
        let uu____3972 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3972 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___157_3976 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___157_3976.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___157_3976.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___157_3976.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___158_3983 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___158_3983.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___158_3983.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___158_3983.FStar_Syntax_Syntax.vars)
                })
         | uu____3988 -> None)
    | uu____3989 -> failwith "Unexpected number of arguments" in
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
      let uu____4000 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops cfg.steps) in
      if uu____4000
      then tm
      else
        (let uu____4002 = FStar_Syntax_Util.head_and_args tm in
         match uu____4002 with
         | (head1,args) ->
             let uu____4028 =
               let uu____4029 = FStar_Syntax_Util.un_uinst head1 in
               uu____4029.FStar_Syntax_Syntax.n in
             (match uu____4028 with
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____4033 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps in
                  (match uu____4033 with
                   | None  -> tm
                   | Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then tm
                       else
                         (let uu____4045 =
                            prim_step.interpretation
                              head1.FStar_Syntax_Syntax.pos args in
                          match uu____4045 with
                          | None  -> tm
                          | Some reduced -> reduced))
              | uu____4048 -> tm))
let reduce_equality:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___159_4055 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___159_4055.tcenv);
           delta_level = (uu___159_4055.delta_level);
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
        let uu___160_4077 = t in
        {
          FStar_Syntax_Syntax.n = (uu___160_4077.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___160_4077.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___160_4077.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid ->
            Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid ->
            Some false
        | uu____4096 -> None in
      let simplify arg = ((simp_t (fst arg)), arg) in
      let uu____4123 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps) in
      if uu____4123
      then reduce_primops cfg tm
      else
        (match tm.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.tk = uu____4126;
                     FStar_Syntax_Syntax.pos = uu____4127;
                     FStar_Syntax_Syntax.vars = uu____4128;_},uu____4129);
                FStar_Syntax_Syntax.tk = uu____4130;
                FStar_Syntax_Syntax.pos = uu____4131;
                FStar_Syntax_Syntax.vars = uu____4132;_},args)
             ->
             let uu____4152 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____4152
             then
               let uu____4153 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____4153 with
                | (Some (true ),uu____4186)::(uu____4187,(arg,uu____4189))::[]
                    -> arg
                | (uu____4230,(arg,uu____4232))::(Some (true ),uu____4233)::[]
                    -> arg
                | (Some (false ),uu____4274)::uu____4275::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4313::(Some (false ),uu____4314)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4352 -> tm)
             else
               (let uu____4362 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____4362
                then
                  let uu____4363 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____4363 with
                  | (Some (true ),uu____4396)::uu____4397::[] ->
                      w FStar_Syntax_Util.t_true
                  | uu____4435::(Some (true ),uu____4436)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),uu____4474)::(uu____4475,(arg,uu____4477))::[]
                      -> arg
                  | (uu____4518,(arg,uu____4520))::(Some (false ),uu____4521)::[]
                      -> arg
                  | uu____4562 -> tm
                else
                  (let uu____4572 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____4572
                   then
                     let uu____4573 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____4573 with
                     | uu____4606::(Some (true ),uu____4607)::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (false ),uu____4645)::uu____4646::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____4684)::(uu____4685,(arg,uu____4687))::[]
                         -> arg
                     | uu____4728 -> tm
                   else
                     (let uu____4738 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____4738
                      then
                        let uu____4739 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____4739 with
                        | (Some (true ),uu____4772)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____4796)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____4820 -> tm
                      else
                        (let uu____4830 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid in
                         if uu____4830
                         then
                           match args with
                           | (t,uu____4832)::[] ->
                               let uu____4845 =
                                 let uu____4846 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____4846.FStar_Syntax_Syntax.n in
                               (match uu____4845 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____4849::[],body,uu____4851) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____4877 -> tm)
                                | uu____4879 -> tm)
                           | (uu____4880,Some (FStar_Syntax_Syntax.Implicit
                              uu____4881))::(t,uu____4883)::[] ->
                               let uu____4910 =
                                 let uu____4911 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____4911.FStar_Syntax_Syntax.n in
                               (match uu____4910 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____4914::[],body,uu____4916) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____4942 -> tm)
                                | uu____4944 -> tm)
                           | uu____4945 -> tm
                         else
                           (let uu____4952 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid in
                            if uu____4952
                            then
                              match args with
                              | (t,uu____4954)::[] ->
                                  let uu____4967 =
                                    let uu____4968 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____4968.FStar_Syntax_Syntax.n in
                                  (match uu____4967 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____4971::[],body,uu____4973) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____4999 -> tm)
                                   | uu____5001 -> tm)
                              | (uu____5002,Some
                                 (FStar_Syntax_Syntax.Implicit uu____5003))::
                                  (t,uu____5005)::[] ->
                                  let uu____5032 =
                                    let uu____5033 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5033.FStar_Syntax_Syntax.n in
                                  (match uu____5032 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5036::[],body,uu____5038) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5064 -> tm)
                                   | uu____5066 -> tm)
                              | uu____5067 -> tm
                            else reduce_equality cfg tm)))))
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                FStar_Syntax_Syntax.tk = uu____5075;
                FStar_Syntax_Syntax.pos = uu____5076;
                FStar_Syntax_Syntax.vars = uu____5077;_},args)
             ->
             let uu____5093 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____5093
             then
               let uu____5094 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____5094 with
                | (Some (true ),uu____5127)::(uu____5128,(arg,uu____5130))::[]
                    -> arg
                | (uu____5171,(arg,uu____5173))::(Some (true ),uu____5174)::[]
                    -> arg
                | (Some (false ),uu____5215)::uu____5216::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____5254::(Some (false ),uu____5255)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____5293 -> tm)
             else
               (let uu____5303 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____5303
                then
                  let uu____5304 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____5304 with
                  | (Some (true ),uu____5337)::uu____5338::[] ->
                      w FStar_Syntax_Util.t_true
                  | uu____5376::(Some (true ),uu____5377)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),uu____5415)::(uu____5416,(arg,uu____5418))::[]
                      -> arg
                  | (uu____5459,(arg,uu____5461))::(Some (false ),uu____5462)::[]
                      -> arg
                  | uu____5503 -> tm
                else
                  (let uu____5513 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____5513
                   then
                     let uu____5514 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____5514 with
                     | uu____5547::(Some (true ),uu____5548)::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (false ),uu____5586)::uu____5587::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____5625)::(uu____5626,(arg,uu____5628))::[]
                         -> arg
                     | uu____5669 -> tm
                   else
                     (let uu____5679 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____5679
                      then
                        let uu____5680 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____5680 with
                        | (Some (true ),uu____5713)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____5737)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____5761 -> tm
                      else
                        (let uu____5771 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid in
                         if uu____5771
                         then
                           match args with
                           | (t,uu____5773)::[] ->
                               let uu____5786 =
                                 let uu____5787 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5787.FStar_Syntax_Syntax.n in
                               (match uu____5786 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5790::[],body,uu____5792) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5818 -> tm)
                                | uu____5820 -> tm)
                           | (uu____5821,Some (FStar_Syntax_Syntax.Implicit
                              uu____5822))::(t,uu____5824)::[] ->
                               let uu____5851 =
                                 let uu____5852 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5852.FStar_Syntax_Syntax.n in
                               (match uu____5851 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5855::[],body,uu____5857) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5883 -> tm)
                                | uu____5885 -> tm)
                           | uu____5886 -> tm
                         else
                           (let uu____5893 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid in
                            if uu____5893
                            then
                              match args with
                              | (t,uu____5895)::[] ->
                                  let uu____5908 =
                                    let uu____5909 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5909.FStar_Syntax_Syntax.n in
                                  (match uu____5908 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5912::[],body,uu____5914) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5940 -> tm)
                                   | uu____5942 -> tm)
                              | (uu____5943,Some
                                 (FStar_Syntax_Syntax.Implicit uu____5944))::
                                  (t,uu____5946)::[] ->
                                  let uu____5973 =
                                    let uu____5974 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5974.FStar_Syntax_Syntax.n in
                                  (match uu____5973 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5977::[],body,uu____5979) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____6005 -> tm)
                                   | uu____6007 -> tm)
                              | uu____6008 -> tm
                            else reduce_equality cfg tm)))))
         | uu____6015 -> tm)
let is_norm_request hd1 args =
  let uu____6030 =
    let uu____6034 =
      let uu____6035 = FStar_Syntax_Util.un_uinst hd1 in
      uu____6035.FStar_Syntax_Syntax.n in
    (uu____6034, args) in
  match uu____6030 with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6040::uu____6041::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize_term
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6044::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize
  | uu____6046 -> false
let get_norm_request args =
  match args with
  | uu____6065::(tm,uu____6067)::[] -> tm
  | (tm,uu____6077)::[] -> tm
  | uu____6082 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___135_6089  ->
    match uu___135_6089 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.tk = uu____6091;
           FStar_Syntax_Syntax.pos = uu____6092;
           FStar_Syntax_Syntax.vars = uu____6093;_},uu____6094,uu____6095))::uu____6096
        -> true
    | uu____6102 -> false
let is_fstar_tactics_embed: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____6107 =
      let uu____6108 = FStar_Syntax_Util.un_uinst t in
      uu____6108.FStar_Syntax_Syntax.n in
    match uu____6107 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Syntax_Const.fstar_tactics_embed_lid
    | uu____6112 -> false
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
            (fun uu____6226  ->
               let uu____6227 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____6228 = FStar_Syntax_Print.term_to_string t1 in
               let uu____6229 =
                 let uu____6230 =
                   let uu____6232 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives.fst uu____6232 in
                 stack_to_string uu____6230 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____6227
                 uu____6228 uu____6229);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____6244 ->
               failwith "Impossible"
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____6265 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____6274 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____6275 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6276;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____6277;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6282;
                 FStar_Syntax_Syntax.fv_delta = uu____6283;
                 FStar_Syntax_Syntax.fv_qual = Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6287;
                 FStar_Syntax_Syntax.fv_delta = uu____6288;
                 FStar_Syntax_Syntax.fv_qual = Some
                   (FStar_Syntax_Syntax.Record_ctor uu____6289);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.tk = uu____6297;
                  FStar_Syntax_Syntax.pos = uu____6298;
                  FStar_Syntax_Syntax.vars = uu____6299;_},uu____6300)
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Syntax_Const.fstar_tactics_embed_lid
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               is_fstar_tactics_embed hd1 ->
               let args1 = closures_as_args_delayed cfg env args in
               let t2 =
                 let uu___161_6340 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd1, args1));
                   FStar_Syntax_Syntax.tk =
                     (uu___161_6340.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___161_6340.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___161_6340.FStar_Syntax_Syntax.vars)
                 } in
               let t3 = reduce_primops cfg t2 in rebuild cfg env stack1 t3
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____6369 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____6369) && (is_norm_request hd1 args))
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
                 let uu___162_6382 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___162_6382.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___162_6382.primitive_steps)
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
                  FStar_Syntax_Syntax.tk = uu____6387;
                  FStar_Syntax_Syntax.pos = uu____6388;
                  FStar_Syntax_Syntax.vars = uu____6389;_},a1::a2::rest)
               ->
               let uu____6423 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6423 with
                | (hd1,uu____6434) ->
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
                    (FStar_Const.Const_reflect uu____6489);
                  FStar_Syntax_Syntax.tk = uu____6490;
                  FStar_Syntax_Syntax.pos = uu____6491;
                  FStar_Syntax_Syntax.vars = uu____6492;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____6515 = FStar_List.tl stack1 in
               norm cfg env uu____6515 (fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.tk = uu____6518;
                  FStar_Syntax_Syntax.pos = uu____6519;
                  FStar_Syntax_Syntax.vars = uu____6520;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____6543 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6543 with
                | (reify_head,uu____6554) ->
                    let a1 =
                      let uu____6570 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (fst a) in
                      FStar_Syntax_Subst.compress uu____6570 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____6573);
                            FStar_Syntax_Syntax.tk = uu____6574;
                            FStar_Syntax_Syntax.pos = uu____6575;
                            FStar_Syntax_Syntax.vars = uu____6576;_},a2::[])
                         -> norm cfg env stack1 (fst a2)
                     | uu____6601 ->
                         let stack2 =
                           (App
                              (reify_head, None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____6609 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____6609
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____6616 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____6616
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____6619 =
                      let uu____6623 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____6623, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____6619 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___136_6632  ->
                         match uu___136_6632 with
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
                    let uu____6636 = FStar_Syntax_Syntax.range_of_fv f in
                    FStar_TypeChecker_Env.set_range cfg.tcenv uu____6636 in
                  let uu____6637 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  match uu____6637 with
                  | None  ->
                      (log cfg
                         (fun uu____6648  ->
                            FStar_Util.print "Tm_fvar case 2\n" []);
                       rebuild cfg env stack1 t1)
                  | Some (us,t2) ->
                      (log cfg
                         (fun uu____6654  ->
                            let uu____6655 =
                              FStar_Syntax_Print.term_to_string t0 in
                            let uu____6656 =
                              FStar_Syntax_Print.term_to_string t2 in
                            FStar_Util.print2 ">>> Unfolded %s to %s\n"
                              uu____6655 uu____6656);
                       (let t3 =
                          let uu____6658 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 (UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant)) in
                          if uu____6658
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
                          | (UnivArgs (us',uu____6670))::stack2 ->
                              let env1 =
                                FStar_All.pipe_right us'
                                  (FStar_List.fold_left
                                     (fun env1  -> fun u  -> (Univ u) :: env1)
                                     env) in
                              norm cfg env1 stack2 t3
                          | uu____6683 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack1 t3
                          | uu____6684 ->
                              let uu____6685 =
                                let uu____6686 =
                                  FStar_Syntax_Print.lid_to_string
                                    (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                FStar_Util.format1
                                  "Impossible: missing universe instantiation on %s"
                                  uu____6686 in
                              failwith uu____6685
                        else norm cfg env stack1 t3)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____6693 = lookup_bvar env x in
               (match uu____6693 with
                | Univ uu____6694 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____6709 = FStar_ST.read r in
                      (match uu____6709 with
                       | Some (env2,t') ->
                           (log cfg
                              (fun uu____6728  ->
                                 let uu____6729 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____6730 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____6729
                                   uu____6730);
                            (let uu____6731 =
                               let uu____6732 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____6732.FStar_Syntax_Syntax.n in
                             match uu____6731 with
                             | FStar_Syntax_Syntax.Tm_abs uu____6735 ->
                                 norm cfg env2 stack1 t'
                             | uu____6750 -> rebuild cfg env2 stack1 t'))
                       | None  -> norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____6783)::uu____6784 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____6789)::uu____6790 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____6796,uu____6797))::stack_rest ->
                    (match c with
                     | Univ uu____6800 -> norm cfg (c :: env) stack_rest t1
                     | uu____6801 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____6804::[] ->
                              (match lopt with
                               | None  when FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____6817  ->
                                         let uu____6818 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6818);
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
                                           (fun uu___137_6832  ->
                                              match uu___137_6832 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____6833 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____6835  ->
                                         let uu____6836 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6836);
                                    norm cfg (c :: env) stack_rest body)
                               | Some (FStar_Util.Inl lc) when
                                   FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                                   ->
                                   (log cfg
                                      (fun uu____6847  ->
                                         let uu____6848 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6848);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____6849 when
                                   FStar_All.pipe_right cfg.steps
                                     (FStar_List.contains Reify)
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____6856 ->
                                   let cfg1 =
                                     let uu___163_6864 = cfg in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___163_6864.tcenv);
                                       delta_level =
                                         (uu___163_6864.delta_level);
                                       primitive_steps =
                                         (uu___163_6864.primitive_steps)
                                     } in
                                   let uu____6865 =
                                     closure_as_term cfg1 env t1 in
                                   rebuild cfg1 env stack1 uu____6865)
                          | uu____6866::tl1 ->
                              (log cfg
                                 (fun uu____6876  ->
                                    let uu____6877 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____6877);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___164_6901 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___164_6901.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____6914  ->
                          let uu____6915 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____6915);
                     norm cfg env stack2 t1)
                | (Debug uu____6916)::uu____6917 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____6919 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____6919
                    else
                      (let uu____6921 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____6921 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____6950 =
                                   let uu____6956 =
                                     let uu____6957 =
                                       let uu____6958 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____6958 in
                                     FStar_All.pipe_right uu____6957
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____6956
                                     (fun _0_31  -> FStar_Util.Inl _0_31) in
                                 FStar_All.pipe_right uu____6950
                                   (fun _0_32  -> Some _0_32)
                             | uu____6983 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____6997  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7002  ->
                                 let uu____7003 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7003);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___165_7013 = cfg in
                               let uu____7014 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___165_7013.steps);
                                 tcenv = (uu___165_7013.tcenv);
                                 delta_level = (uu___165_7013.delta_level);
                                 primitive_steps = uu____7014
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____7024)::uu____7025 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7029 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7029
                    else
                      (let uu____7031 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7031 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7060 =
                                   let uu____7066 =
                                     let uu____7067 =
                                       let uu____7068 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7068 in
                                     FStar_All.pipe_right uu____7067
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7066
                                     (fun _0_33  -> FStar_Util.Inl _0_33) in
                                 FStar_All.pipe_right uu____7060
                                   (fun _0_34  -> Some _0_34)
                             | uu____7093 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7107  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7112  ->
                                 let uu____7113 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7113);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___165_7123 = cfg in
                               let uu____7124 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___165_7123.steps);
                                 tcenv = (uu___165_7123.tcenv);
                                 delta_level = (uu___165_7123.delta_level);
                                 primitive_steps = uu____7124
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____7134)::uu____7135 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7141 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7141
                    else
                      (let uu____7143 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7143 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7172 =
                                   let uu____7178 =
                                     let uu____7179 =
                                       let uu____7180 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7180 in
                                     FStar_All.pipe_right uu____7179
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7178
                                     (fun _0_35  -> FStar_Util.Inl _0_35) in
                                 FStar_All.pipe_right uu____7172
                                   (fun _0_36  -> Some _0_36)
                             | uu____7205 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7219  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7224  ->
                                 let uu____7225 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7225);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___165_7235 = cfg in
                               let uu____7236 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___165_7235.steps);
                                 tcenv = (uu___165_7235.tcenv);
                                 delta_level = (uu___165_7235.delta_level);
                                 primitive_steps = uu____7236
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____7246)::uu____7247 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7252 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7252
                    else
                      (let uu____7254 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7254 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7283 =
                                   let uu____7289 =
                                     let uu____7290 =
                                       let uu____7291 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7291 in
                                     FStar_All.pipe_right uu____7290
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7289
                                     (fun _0_37  -> FStar_Util.Inl _0_37) in
                                 FStar_All.pipe_right uu____7283
                                   (fun _0_38  -> Some _0_38)
                             | uu____7316 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7330  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7335  ->
                                 let uu____7336 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7336);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___165_7346 = cfg in
                               let uu____7347 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___165_7346.steps);
                                 tcenv = (uu___165_7346.tcenv);
                                 delta_level = (uu___165_7346.delta_level);
                                 primitive_steps = uu____7347
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____7357)::uu____7358 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7368 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7368
                    else
                      (let uu____7370 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7370 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7399 =
                                   let uu____7405 =
                                     let uu____7406 =
                                       let uu____7407 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7407 in
                                     FStar_All.pipe_right uu____7406
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7405
                                     (fun _0_39  -> FStar_Util.Inl _0_39) in
                                 FStar_All.pipe_right uu____7399
                                   (fun _0_40  -> Some _0_40)
                             | uu____7432 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7446  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7451  ->
                                 let uu____7452 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7452);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___165_7462 = cfg in
                               let uu____7463 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___165_7462.steps);
                                 tcenv = (uu___165_7462.tcenv);
                                 delta_level = (uu___165_7462.delta_level);
                                 primitive_steps = uu____7463
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7473 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7473
                    else
                      (let uu____7475 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7475 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7504 =
                                   let uu____7510 =
                                     let uu____7511 =
                                       let uu____7512 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7512 in
                                     FStar_All.pipe_right uu____7511
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7510
                                     (fun _0_41  -> FStar_Util.Inl _0_41) in
                                 FStar_All.pipe_right uu____7504
                                   (fun _0_42  -> Some _0_42)
                             | uu____7537 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7551  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7556  ->
                                 let uu____7557 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7557);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___165_7567 = cfg in
                               let uu____7568 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___165_7567.steps);
                                 tcenv = (uu___165_7567.tcenv);
                                 delta_level = (uu___165_7567.delta_level);
                                 primitive_steps = uu____7568
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
                      (fun uu____7600  ->
                         fun stack2  ->
                           match uu____7600 with
                           | (a,aq) ->
                               let uu____7608 =
                                 let uu____7609 =
                                   let uu____7613 =
                                     let uu____7614 =
                                       let uu____7624 =
                                         FStar_Util.mk_ref None in
                                       (env, a, uu____7624, false) in
                                     Clos uu____7614 in
                                   (uu____7613, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____7609 in
                               uu____7608 :: stack2) args) in
               (log cfg
                  (fun uu____7646  ->
                     let uu____7647 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____7647);
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
                             ((let uu___166_7668 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___166_7668.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___166_7668.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____7669 ->
                      let uu____7672 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7672)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____7675 = FStar_Syntax_Subst.open_term [(x, None)] f in
                  match uu____7675 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____7691 =
                          let uu____7692 =
                            let uu____7697 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___167_7698 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___167_7698.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___167_7698.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____7697) in
                          FStar_Syntax_Syntax.Tm_refine uu____7692 in
                        mk uu____7691 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____7711 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____7711
               else
                 (let uu____7713 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____7713 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____7719 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  -> fun uu____7725  -> Dummy :: env1)
                               env) in
                        norm_comp cfg uu____7719 c1 in
                      let t2 =
                        let uu____7732 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____7732 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____7775)::uu____7776 -> norm cfg env stack1 t11
                | (Arg uu____7781)::uu____7782 -> norm cfg env stack1 t11
                | (App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.tk = uu____7787;
                       FStar_Syntax_Syntax.pos = uu____7788;
                       FStar_Syntax_Syntax.vars = uu____7789;_},uu____7790,uu____7791))::uu____7792
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____7798)::uu____7799 ->
                    norm cfg env stack1 t11
                | uu____7804 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____7807  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____7820 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____7820
                        | FStar_Util.Inr c ->
                            let uu____7828 = norm_comp cfg env c in
                            FStar_Util.Inr uu____7828 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____7833 =
                        mk
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (t12, (tc1, tacopt1), l))
                          t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____7833)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____7884,{
                              FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                uu____7885;
                              FStar_Syntax_Syntax.lbunivs = uu____7886;
                              FStar_Syntax_Syntax.lbtyp = uu____7887;
                              FStar_Syntax_Syntax.lbeff = uu____7888;
                              FStar_Syntax_Syntax.lbdef = uu____7889;_}::uu____7890),uu____7891)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____7917 =
                 (let uu____7918 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____7918) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____7919 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____7919))) in
               if uu____7917
               then
                 let env1 =
                   let uu____7922 =
                     let uu____7923 =
                       let uu____7933 = FStar_Util.mk_ref None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____7933,
                         false) in
                     Clos uu____7923 in
                   uu____7922 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____7957 =
                    let uu____7960 =
                      let uu____7961 =
                        let uu____7962 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____7962
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____7961] in
                    FStar_Syntax_Subst.open_term uu____7960 body in
                  match uu____7957 with
                  | (bs,body1) ->
                      let lb1 =
                        let uu___168_7968 = lb in
                        let uu____7969 =
                          let uu____7972 =
                            let uu____7973 = FStar_List.hd bs in
                            FStar_All.pipe_right uu____7973
                              FStar_Pervasives.fst in
                          FStar_All.pipe_right uu____7972
                            (fun _0_43  -> FStar_Util.Inl _0_43) in
                        let uu____7982 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____7985 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = uu____7969;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___168_7968.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____7982;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___168_7968.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____7985
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____7995  -> Dummy :: env1)
                             env) in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____8011 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____8011
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____8024 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____8046  ->
                        match uu____8046 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____8085 =
                                let uu___169_8086 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___169_8086.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___169_8086.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____8085 in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos in
                            let memo = FStar_Util.mk_ref None in
                            let rec_env1 = (Clos (env, fix_f_i, memo, true))
                              :: rec_env in
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1")))) (snd lbs)
                   (env, [], (Prims.parse_int "0")) in
               (match uu____8024 with
                | (rec_env,memos,uu____8146) ->
                    let uu____8161 =
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
                             let uu____8203 =
                               let uu____8204 =
                                 let uu____8214 = FStar_Util.mk_ref None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____8214, false) in
                               Clos uu____8204 in
                             uu____8203 :: env1) (snd lbs) env in
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
                             FStar_Syntax_Syntax.tk = uu____8252;
                             FStar_Syntax_Syntax.pos = uu____8253;
                             FStar_Syntax_Syntax.vars = uu____8254;_},uu____8255,uu____8256))::uu____8257
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____8263 -> false in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____8270 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____8270
                        then
                          let uu___170_8271 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___170_8271.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps = (uu___170_8271.primitive_steps)
                          }
                        else
                          (let uu___171_8273 = cfg in
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___171_8273.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta];
                             primitive_steps =
                               (uu___171_8273.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____8275 =
                         let uu____8276 = FStar_Syntax_Subst.compress head1 in
                         uu____8276.FStar_Syntax_Syntax.n in
                       match uu____8275 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____8290 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8290 with
                            | (uu____8291,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____8295 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____8302 =
                                         let uu____8303 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____8303.FStar_Syntax_Syntax.n in
                                       match uu____8302 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____8308,uu____8309))
                                           ->
                                           let uu____8318 =
                                             let uu____8319 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____8319.FStar_Syntax_Syntax.n in
                                           (match uu____8318 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____8324,msrc,uu____8326))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____8335 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                Some uu____8335
                                            | uu____8336 -> None)
                                       | uu____8337 -> None in
                                     let uu____8338 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____8338 with
                                      | Some e ->
                                          let lb1 =
                                            let uu___172_8342 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___172_8342.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___172_8342.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___172_8342.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Syntax_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____8343 =
                                            FStar_List.tl stack1 in
                                          let uu____8344 =
                                            let uu____8345 =
                                              let uu____8348 =
                                                let uu____8349 =
                                                  let uu____8357 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____8357) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____8349 in
                                              FStar_Syntax_Syntax.mk
                                                uu____8348 in
                                            uu____8345 None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____8343 uu____8344
                                      | None  ->
                                          let uu____8374 =
                                            let uu____8375 = is_return body in
                                            match uu____8375 with
                                            | Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____8378;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____8379;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____8380;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____8385 -> false in
                                          if uu____8374
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
                                               let uu____8405 =
                                                 let uu____8408 =
                                                   let uu____8409 =
                                                     let uu____8424 =
                                                       let uu____8426 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____8426] in
                                                     (uu____8424, body1,
                                                       (Some
                                                          (FStar_Util.Inr
                                                             (m1, [])))) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____8409 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8408 in
                                               uu____8405 None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____8459 =
                                                 let uu____8460 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____8460.FStar_Syntax_Syntax.n in
                                               match uu____8459 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____8466::uu____8467::[])
                                                   ->
                                                   let uu____8473 =
                                                     let uu____8476 =
                                                       let uu____8477 =
                                                         let uu____8482 =
                                                           let uu____8484 =
                                                             let uu____8485 =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____8485 in
                                                           let uu____8486 =
                                                             let uu____8488 =
                                                               let uu____8489
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____8489 in
                                                             [uu____8488] in
                                                           uu____8484 ::
                                                             uu____8486 in
                                                         (bind1, uu____8482) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____8477 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8476 in
                                                   uu____8473 None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____8501 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____8507 =
                                                 let uu____8510 =
                                                   let uu____8511 =
                                                     let uu____8521 =
                                                       let uu____8523 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____8524 =
                                                         let uu____8526 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____8527 =
                                                           let uu____8529 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____8530 =
                                                             let uu____8532 =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____8533 =
                                                               let uu____8535
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____8536
                                                                 =
                                                                 let uu____8538
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____8538] in
                                                               uu____8535 ::
                                                                 uu____8536 in
                                                             uu____8532 ::
                                                               uu____8533 in
                                                           uu____8529 ::
                                                             uu____8530 in
                                                         uu____8526 ::
                                                           uu____8527 in
                                                       uu____8523 ::
                                                         uu____8524 in
                                                     (bind_inst, uu____8521) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____8511 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8510 in
                                               uu____8507 None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____8550 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____8550 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____8568 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8568 with
                            | (uu____8569,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____8592 =
                                        let uu____8593 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____8593.FStar_Syntax_Syntax.n in
                                      match uu____8592 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____8599) -> t4
                                      | uu____8604 -> head2 in
                                    let uu____8605 =
                                      let uu____8606 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____8606.FStar_Syntax_Syntax.n in
                                    match uu____8605 with
                                    | FStar_Syntax_Syntax.Tm_fvar x -> Some x
                                    | uu____8611 -> None in
                                  let uu____8612 = maybe_extract_fv head2 in
                                  match uu____8612 with
                                  | Some x when
                                      let uu____8618 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____8618
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____8622 =
                                          maybe_extract_fv head3 in
                                        match uu____8622 with
                                        | Some uu____8625 -> Some true
                                        | uu____8626 -> Some false in
                                      (head3, action_unfolded)
                                  | uu____8629 -> (head2, None) in
                                ((let is_arg_impure uu____8640 =
                                    match uu____8640 with
                                    | (e,q) ->
                                        let uu____8645 =
                                          let uu____8646 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____8646.FStar_Syntax_Syntax.n in
                                        (match uu____8645 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____8661 -> false) in
                                  let uu____8662 =
                                    let uu____8663 =
                                      let uu____8667 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____8667 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____8663 in
                                  if uu____8662
                                  then
                                    let uu____8670 =
                                      let uu____8671 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____8671 in
                                    failwith uu____8670
                                  else ());
                                 (let uu____8673 =
                                    maybe_unfold_action head_app in
                                  match uu____8673 with
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
                                      let uu____8708 = FStar_List.tl stack1 in
                                      norm cfg env uu____8708 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____8722 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____8722 in
                           let uu____8723 = FStar_List.tl stack1 in
                           norm cfg env uu____8723 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____8806  ->
                                     match uu____8806 with
                                     | (pat,wopt,tm) ->
                                         let uu____8844 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____8844))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____8870 = FStar_List.tl stack1 in
                           norm cfg env uu____8870 tm
                       | uu____8871 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.tk = uu____8880;
                             FStar_Syntax_Syntax.pos = uu____8881;
                             FStar_Syntax_Syntax.vars = uu____8882;_},uu____8883,uu____8884))::uu____8885
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____8891 -> false in
                    if should_reify
                    then
                      let uu____8892 = FStar_List.tl stack1 in
                      let uu____8893 =
                        let uu____8894 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____8894 in
                      norm cfg env uu____8892 uu____8893
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____8897 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____8897
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___173_8903 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___173_8903.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___173_8903.primitive_steps)
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
                | uu____8905 ->
                    (match stack1 with
                     | uu____8906::uu____8907 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____8911)
                              -> norm cfg env ((Meta (m, r)) :: stack1) head1
                          | FStar_Syntax_Syntax.Meta_pattern args ->
                              let args1 = norm_pattern_args cfg env args in
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_pattern args1),
                                      (t1.FStar_Syntax_Syntax.pos))) ::
                                stack1) head1
                          | uu____8926 -> norm cfg env stack1 head1)
                     | [] ->
                         let head2 = norm cfg env [] head1 in
                         let m1 =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               let uu____8936 =
                                 norm_pattern_args cfg env args in
                               FStar_Syntax_Syntax.Meta_pattern uu____8936
                           | uu____8943 -> m in
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
              let uu____8955 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____8955 with
              | (uu____8956,return_repr) ->
                  let return_inst =
                    let uu____8963 =
                      let uu____8964 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____8964.FStar_Syntax_Syntax.n in
                    match uu____8963 with
                    | FStar_Syntax_Syntax.Tm_uinst (return_tm,uu____8970::[])
                        ->
                        let uu____8976 =
                          let uu____8979 =
                            let uu____8980 =
                              let uu____8985 =
                                let uu____8987 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____8987] in
                              (return_tm, uu____8985) in
                            FStar_Syntax_Syntax.Tm_uinst uu____8980 in
                          FStar_Syntax_Syntax.mk uu____8979 in
                        uu____8976 None e.FStar_Syntax_Syntax.pos
                    | uu____8999 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____9002 =
                    let uu____9005 =
                      let uu____9006 =
                        let uu____9016 =
                          let uu____9018 = FStar_Syntax_Syntax.as_arg t in
                          let uu____9019 =
                            let uu____9021 = FStar_Syntax_Syntax.as_arg e in
                            [uu____9021] in
                          uu____9018 :: uu____9019 in
                        (return_inst, uu____9016) in
                      FStar_Syntax_Syntax.Tm_app uu____9006 in
                    FStar_Syntax_Syntax.mk uu____9005 in
                  uu____9002 None e.FStar_Syntax_Syntax.pos
            else
              (let uu____9034 = FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____9034 with
               | None  ->
                   let uu____9036 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____9036
               | Some
                   { FStar_TypeChecker_Env.msource = uu____9037;
                     FStar_TypeChecker_Env.mtarget = uu____9038;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____9039;
                         FStar_TypeChecker_Env.mlift_term = None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | Some
                   { FStar_TypeChecker_Env.msource = uu____9050;
                     FStar_TypeChecker_Env.mtarget = uu____9051;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____9052;
                         FStar_TypeChecker_Env.mlift_term = Some lift;_};_}
                   ->
                   let uu____9070 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____9070)
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
                (fun uu____9100  ->
                   match uu____9100 with
                   | (a,imp) ->
                       let uu____9107 = norm cfg env [] a in
                       (uu____9107, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___174_9122 = comp1 in
            let uu____9125 =
              let uu____9126 =
                let uu____9132 = norm cfg env [] t in
                let uu____9133 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____9132, uu____9133) in
              FStar_Syntax_Syntax.Total uu____9126 in
            {
              FStar_Syntax_Syntax.n = uu____9125;
              FStar_Syntax_Syntax.tk = (uu___174_9122.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___174_9122.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___174_9122.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___175_9148 = comp1 in
            let uu____9151 =
              let uu____9152 =
                let uu____9158 = norm cfg env [] t in
                let uu____9159 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____9158, uu____9159) in
              FStar_Syntax_Syntax.GTotal uu____9152 in
            {
              FStar_Syntax_Syntax.n = uu____9151;
              FStar_Syntax_Syntax.tk = (uu___175_9148.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___175_9148.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___175_9148.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____9190  ->
                      match uu____9190 with
                      | (a,i) ->
                          let uu____9197 = norm cfg env [] a in
                          (uu____9197, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___138_9202  ->
                      match uu___138_9202 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____9206 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____9206
                      | f -> f)) in
            let uu___176_9210 = comp1 in
            let uu____9213 =
              let uu____9214 =
                let uu___177_9215 = ct in
                let uu____9216 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____9217 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____9220 = norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____9216;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___177_9215.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____9217;
                  FStar_Syntax_Syntax.effect_args = uu____9220;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____9214 in
            {
              FStar_Syntax_Syntax.n = uu____9213;
              FStar_Syntax_Syntax.tk = (uu___176_9210.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___176_9210.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___176_9210.FStar_Syntax_Syntax.vars)
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
            (let uu___178_9237 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___178_9237.tcenv);
               delta_level = (uu___178_9237.delta_level);
               primitive_steps = (uu___178_9237.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____9242 = norm1 t in
          FStar_Syntax_Util.non_informative uu____9242 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____9245 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___179_9259 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.tk = (uu___179_9259.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___179_9259.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___179_9259.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____9269 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____9269
            then
              let ct1 =
                match downgrade_ghost_effect_name
                        ct.FStar_Syntax_Syntax.effect_name
                with
                | Some pure_eff ->
                    let uu___180_9274 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___180_9274.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___180_9274.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___180_9274.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___180_9274.FStar_Syntax_Syntax.flags)
                    }
                | None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___181_9276 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___181_9276.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Syntax_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___181_9276.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___181_9276.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___181_9276.FStar_Syntax_Syntax.flags)
                    } in
              let uu___182_9277 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.tk =
                  (uu___182_9277.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___182_9277.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___182_9277.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____9283 -> c
and norm_binder:
  cfg ->
    env ->
      FStar_Syntax_Syntax.binder ->
        (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  =
  fun cfg  ->
    fun env  ->
      fun uu____9286  ->
        match uu____9286 with
        | (x,imp) ->
            let uu____9289 =
              let uu___183_9290 = x in
              let uu____9291 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___183_9290.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___183_9290.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____9291
              } in
            (uu____9289, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____9297 =
          FStar_List.fold_left
            (fun uu____9304  ->
               fun b  ->
                 match uu____9304 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____9297 with | (nbs,uu____9321) -> FStar_List.rev nbs
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
            let uu____9338 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
            if uu____9338
            then
              let t = norm cfg env [] lc.FStar_Syntax_Syntax.res_typ in
              let uu____9343 = FStar_Syntax_Util.is_total_lcomp lc in
              (if uu____9343
               then
                 let uu____9347 =
                   let uu____9350 =
                     let uu____9351 =
                       let uu____9354 = FStar_Syntax_Syntax.mk_Total t in
                       FStar_Syntax_Util.comp_set_flags uu____9354 flags in
                     FStar_Syntax_Util.lcomp_of_comp uu____9351 in
                   FStar_Util.Inl uu____9350 in
                 Some uu____9347
               else
                 (let uu____9358 =
                    let uu____9361 =
                      let uu____9362 =
                        let uu____9365 = FStar_Syntax_Syntax.mk_GTotal t in
                        FStar_Syntax_Util.comp_set_flags uu____9365 flags in
                      FStar_Syntax_Util.lcomp_of_comp uu____9362 in
                    FStar_Util.Inl uu____9361 in
                  Some uu____9358))
            else
              Some
                (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags))
        | uu____9378 -> lopt
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
              ((let uu____9390 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____9390
                then
                  let uu____9391 = FStar_Syntax_Print.term_to_string tm in
                  let uu____9392 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2 "Normalized %s to %s\n" uu____9391
                    uu____9392
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___184_9403 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___184_9403.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____9423  ->
                    let uu____9424 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____9424);
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
              let uu____9461 =
                let uu___185_9462 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___185_9462.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___185_9462.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___185_9462.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____9461
          | (Arg (Univ uu____9467,uu____9468,uu____9469))::uu____9470 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____9472,uu____9473))::uu____9474 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____9486),aq,r))::stack2 ->
              (log cfg
                 (fun uu____9502  ->
                    let uu____9503 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____9503);
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
                 (let uu____9514 = FStar_ST.read m in
                  match uu____9514 with
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
                  | Some (uu____9540,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq) None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.extend_app head1 (t, aq) None r in
              let uu____9562 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____9562
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____9569  ->
                    let uu____9570 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____9570);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____9575 =
                  log cfg
                    (fun uu____9577  ->
                       let uu____9578 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____9579 =
                         let uu____9580 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____9587  ->
                                   match uu____9587 with
                                   | (p,uu____9593,uu____9594) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____9580
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____9578 uu____9579);
                  (let whnf = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___139_9604  ->
                               match uu___139_9604 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____9605 -> false)) in
                     let steps' =
                       let uu____9608 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____9608
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___186_9611 = cfg in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___186_9611.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___186_9611.primitive_steps)
                     } in
                   let norm_or_whnf env2 t1 =
                     if whnf
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____9645 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_disj [] ->
                         failwith "Impossible"
                     | FStar_Syntax_Syntax.Pat_disj (hd1::tl1) ->
                         let uu____9665 = norm_pat env2 hd1 in
                         (match uu____9665 with
                          | (hd2,env') ->
                              let tl2 =
                                FStar_All.pipe_right tl1
                                  (FStar_List.map
                                     (fun p1  ->
                                        let uu____9701 = norm_pat env2 p1 in
                                        fst uu____9701)) in
                              ((let uu___187_9713 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_disj (hd2 ::
                                       tl2));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___187_9713.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___187_9713.FStar_Syntax_Syntax.p)
                                }), env'))
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____9730 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____9764  ->
                                   fun uu____9765  ->
                                     match (uu____9764, uu____9765) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____9830 = norm_pat env3 p1 in
                                         (match uu____9830 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____9730 with
                          | (pats1,env3) ->
                              ((let uu___188_9896 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___188_9896.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___188_9896.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___189_9910 = x in
                           let uu____9911 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___189_9910.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___189_9910.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9911
                           } in
                         ((let uu___190_9917 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___190_9917.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___190_9917.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___191_9922 = x in
                           let uu____9923 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___191_9922.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___191_9922.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9923
                           } in
                         ((let uu___192_9929 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___192_9929.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___192_9929.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___193_9939 = x in
                           let uu____9940 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___193_9939.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___193_9939.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9940
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___194_9947 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.ty =
                               (uu___194_9947.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___194_9947.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf -> branches
                     | uu____9951 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____9954 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____9954 with
                                 | (p,wopt,e) ->
                                     let uu____9972 = norm_pat env1 p in
                                     (match uu____9972 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | None  -> None
                                            | Some w ->
                                                let uu____9996 =
                                                  norm_or_whnf env2 w in
                                                Some uu____9996 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____10001 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____10001) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____10011) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____10016 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____10017;
                        FStar_Syntax_Syntax.fv_delta = uu____10018;
                        FStar_Syntax_Syntax.fv_qual = Some
                          (FStar_Syntax_Syntax.Data_ctor );_}
                      -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____10022;
                        FStar_Syntax_Syntax.fv_delta = uu____10023;
                        FStar_Syntax_Syntax.fv_qual = Some
                          (FStar_Syntax_Syntax.Record_ctor uu____10024);_}
                      -> true
                  | uu____10031 -> false in
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
                  let uu____10130 =
                    FStar_Syntax_Util.head_and_args scrutinee2 in
                  match uu____10130 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_disj ps ->
                           let mopt =
                             FStar_Util.find_map ps
                               (fun p1  ->
                                  let m = matches_pat scrutinee2 p1 in
                                  match m with
                                  | FStar_Util.Inl tms ->
                                      let uu____10211 =
                                        let uu____10222 =
                                          let uu____10231 = FStar_List.hd ps in
                                          (tms, uu____10231, p1) in
                                        FStar_Util.Inl uu____10222 in
                                      Some uu____10211
                                  | FStar_Util.Inr (true ) ->
                                      Some (FStar_Util.Inr true)
                                  | FStar_Util.Inr (false ) -> None) in
                           (match mopt with
                            | None  -> FStar_Util.Inr false
                            | Some (FStar_Util.Inr b) -> FStar_Util.Inr b
                            | Some (FStar_Util.Inl
                                (tms,first_case,matched_pattern)) ->
                                let maybe_permute tms1 =
                                  let uu____10361 =
                                    FStar_Util.physical_equality first_case
                                      matched_pattern in
                                  if uu____10361
                                  then tms1
                                  else
                                    FStar_Syntax_Subst.permute_disjunctive_pattern
                                      first_case matched_pattern tms1 in
                                let uu____10366 = maybe_permute tms in
                                FStar_Util.Inl uu____10366)
                       | FStar_Syntax_Syntax.Pat_var uu____10369 ->
                           FStar_Util.Inl [scrutinee2]
                       | FStar_Syntax_Syntax.Pat_wild uu____10371 ->
                           FStar_Util.Inl [scrutinee2]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____10373 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____10385 ->
                                let uu____10386 =
                                  let uu____10387 = is_cons head1 in
                                  Prims.op_Negation uu____10387 in
                                FStar_Util.Inr uu____10386)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____10401 =
                             let uu____10402 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____10402.FStar_Syntax_Syntax.n in
                           (match uu____10401 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____10409 ->
                                let uu____10410 =
                                  let uu____10411 = is_cons head1 in
                                  Prims.op_Negation uu____10411 in
                                FStar_Util.Inr uu____10410))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____10445)::rest_a,(p1,uu____10448)::rest_p) ->
                      let uu____10476 = matches_pat t1 p1 in
                      (match uu____10476 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____10490 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____10561 = matches_pat scrutinee1 p1 in
                      (match uu____10561 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____10571  ->
                                 let uu____10572 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____10573 =
                                   let uu____10574 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____10574
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____10572 uu____10573);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____10583 =
                                        let uu____10584 =
                                          let uu____10594 =
                                            FStar_Util.mk_ref (Some ([], t1)) in
                                          ([], t1, uu____10594, false) in
                                        Clos uu____10584 in
                                      uu____10583 :: env2) env1 s in
                             let uu____10617 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____10617))) in
                let uu____10618 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____10618
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___140_10632  ->
                match uu___140_10632 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | uu____10635 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____10639 -> d in
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
            let uu___195_10659 = config s e in
            {
              steps = (uu___195_10659.steps);
              tcenv = (uu___195_10659.tcenv);
              delta_level = (uu___195_10659.delta_level);
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
      fun t  -> let uu____10678 = config s e in norm_comp uu____10678 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____10685 = config [] env in norm_universe uu____10685 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun c  ->
      let uu____10692 = config [] env in ghost_to_pure_aux uu____10692 [] c
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
        let uu____10704 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____10704 in
      let uu____10705 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____10705
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | Some pure_eff ->
            let uu___196_10707 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___196_10707.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___196_10707.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____10708  ->
                    let uu____10709 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____10709))
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
            ((let uu____10722 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10722);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____10731 = config [AllowUnboundUniverses] env in
          norm_comp uu____10731 [] c
        with
        | e ->
            ((let uu____10735 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10735);
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
                   let uu____10772 =
                     let uu____10773 =
                       let uu____10778 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____10778) in
                     FStar_Syntax_Syntax.Tm_refine uu____10773 in
                   mk uu____10772 t01.FStar_Syntax_Syntax.pos
               | uu____10783 -> t2)
          | uu____10784 -> t2 in
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
        let uu____10806 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____10806 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____10822 ->
                 let uu____10826 = FStar_Syntax_Util.abs_formals e in
                 (match uu____10826 with
                  | (actuals,uu____10837,uu____10838) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____10860 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____10860 with
                         | (binders,args) ->
                             let uu____10870 =
                               FStar_Syntax_Syntax.mk_Tm_app e args None
                                 e.FStar_Syntax_Syntax.pos in
                             let uu____10873 =
                               let uu____10880 =
                                 FStar_All.pipe_right
                                   (FStar_Syntax_Util.lcomp_of_comp c)
                                   (fun _0_44  -> FStar_Util.Inl _0_44) in
                               FStar_All.pipe_right uu____10880
                                 (fun _0_45  -> Some _0_45) in
                             FStar_Syntax_Util.abs binders uu____10870
                               uu____10873)))
let eta_expand:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____10916 =
        let uu____10920 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
        (uu____10920, (t.FStar_Syntax_Syntax.n)) in
      match uu____10916 with
      | (Some sort,uu____10927) ->
          let uu____10929 = mk sort t.FStar_Syntax_Syntax.pos in
          eta_expand_with_type env t uu____10929
      | (uu____10930,FStar_Syntax_Syntax.Tm_name x) ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____10934 ->
          let uu____10938 = FStar_Syntax_Util.head_and_args t in
          (match uu____10938 with
           | (head1,args) ->
               let uu____10964 =
                 let uu____10965 = FStar_Syntax_Subst.compress head1 in
                 uu____10965.FStar_Syntax_Syntax.n in
               (match uu____10964 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____10968,thead) ->
                    let uu____10982 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____10982 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____11013 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___201_11017 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___201_11017.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___201_11017.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___201_11017.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___201_11017.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___201_11017.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___201_11017.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ = None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___201_11017.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___201_11017.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___201_11017.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___201_11017.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___201_11017.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___201_11017.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___201_11017.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___201_11017.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___201_11017.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___201_11017.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___201_11017.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___201_11017.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___201_11017.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___201_11017.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___201_11017.FStar_TypeChecker_Env.qname_and_index)
                                 }) t in
                            match uu____11013 with
                            | (uu____11018,ty,uu____11020) ->
                                eta_expand_with_type env t ty))
                | uu____11021 ->
                    let uu____11022 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___202_11026 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___202_11026.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___202_11026.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___202_11026.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___202_11026.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___202_11026.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___202_11026.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ = None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___202_11026.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___202_11026.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___202_11026.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___202_11026.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___202_11026.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___202_11026.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___202_11026.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___202_11026.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___202_11026.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___202_11026.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___202_11026.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___202_11026.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___202_11026.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___202_11026.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___202_11026.FStar_TypeChecker_Env.qname_and_index)
                         }) t in
                    (match uu____11022 with
                     | (uu____11027,ty,uu____11029) ->
                         eta_expand_with_type env t ty)))