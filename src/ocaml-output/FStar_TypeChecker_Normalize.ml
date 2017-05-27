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
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____1741 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____1775  ->
                                        fun uu____1776  ->
                                          match (uu____1775, uu____1776) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____1841 =
                                                norm_pat env3 p1 in
                                              (match uu____1841 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____1741 with
                               | (pats1,env3) ->
                                   ((let uu___147_1907 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.ty =
                                         (uu___147_1907.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___147_1907.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___148_1921 = x in
                                let uu____1922 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___148_1921.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___148_1921.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1922
                                } in
                              ((let uu___149_1928 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___149_1928.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___149_1928.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___150_1933 = x in
                                let uu____1934 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___150_1933.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___150_1933.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1934
                                } in
                              ((let uu___151_1940 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___151_1940.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___151_1940.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___152_1950 = x in
                                let uu____1951 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___152_1950.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___152_1950.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1951
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___153_1958 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___153_1958.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___153_1958.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____1961 = norm_pat env1 pat in
                        (match uu____1961 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | None  -> None
                               | Some w ->
                                   let uu____1985 =
                                     closure_as_term cfg env2 w in
                                   Some uu____1985 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____1990 =
                    let uu____1991 =
                      let uu____2007 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____2007) in
                    FStar_Syntax_Syntax.Tm_match uu____1991 in
                  mk uu____1990 t1.FStar_Syntax_Syntax.pos))
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
        | uu____2060 -> closure_as_term cfg env t
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
        | uu____2076 ->
            FStar_List.map
              (fun uu____2086  ->
                 match uu____2086 with
                 | (x,imp) ->
                     let uu____2101 = closure_as_term_delayed cfg env x in
                     (uu____2101, imp)) args
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
        let uu____2113 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____2137  ->
                  fun uu____2138  ->
                    match (uu____2137, uu____2138) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___154_2182 = b in
                          let uu____2183 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___154_2182.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___154_2182.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____2183
                          } in
                        let env2 = Dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____2113 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____2230 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____2242 = closure_as_term_delayed cfg env t in
                 let uu____2243 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____2242 uu____2243
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____2253 = closure_as_term_delayed cfg env t in
                 let uu____2254 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____2253 uu____2254
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
                        (fun uu___133_2270  ->
                           match uu___133_2270 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____2274 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____2274
                           | f -> f)) in
                 let uu____2278 =
                   let uu___155_2279 = c1 in
                   let uu____2280 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____2280;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___155_2279.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____2278)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.cflags Prims.list =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_List.filter
         (fun uu___134_2284  ->
            match uu___134_2284 with
            | FStar_Syntax_Syntax.DECREASES uu____2285 -> false
            | uu____2288 -> true))
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
            let uu____2316 = FStar_Syntax_Util.is_total_lcomp lc in
            if uu____2316
            then
              Some
                (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, flags))
            else
              (let uu____2333 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
               if uu____2333
               then
                 Some
                   (FStar_Util.Inr
                      (FStar_Syntax_Const.effect_GTot_lid, flags))
               else
                 Some
                   (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags)))
        | uu____2359 -> lopt
let built_in_primitive_steps: primitive_step Prims.list =
  let const_as_tm c p = mk (FStar_Syntax_Syntax.Tm_constant c) p in
  let int_as_const p i =
    let uu____2383 =
      let uu____2384 =
        let uu____2390 = FStar_Util.string_of_int i in (uu____2390, None) in
      FStar_Const.Const_int uu____2384 in
    const_as_tm uu____2383 p in
  let bool_as_const p b = const_as_tm (FStar_Const.Const_bool b) p in
  let string_as_const p b =
    const_as_tm
      (FStar_Const.Const_string ((FStar_Util.bytes_of_string b), p)) p in
  let arg_as_int uu____2417 =
    match uu____2417 with
    | (a,uu____2422) ->
        let uu____2424 =
          let uu____2425 = FStar_Syntax_Subst.compress a in
          uu____2425.FStar_Syntax_Syntax.n in
        (match uu____2424 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i,None ))
             ->
             let uu____2435 = FStar_Util.int_of_string i in Some uu____2435
         | uu____2436 -> None) in
  let arg_as_bounded_int uu____2445 =
    match uu____2445 with
    | (a,uu____2452) ->
        let uu____2456 =
          let uu____2457 = FStar_Syntax_Subst.compress a in
          uu____2457.FStar_Syntax_Syntax.n in
        (match uu____2456 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.tk = uu____2464;
                FStar_Syntax_Syntax.pos = uu____2465;
                FStar_Syntax_Syntax.vars = uu____2466;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,None ));
                                                            FStar_Syntax_Syntax.tk
                                                              = uu____2468;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____2469;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____2470;_},uu____2471)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____2502 =
               let uu____2505 = FStar_Util.int_of_string i in
               (fv1, uu____2505) in
             Some uu____2502
         | uu____2508 -> None) in
  let arg_as_bool uu____2517 =
    match uu____2517 with
    | (a,uu____2522) ->
        let uu____2524 =
          let uu____2525 = FStar_Syntax_Subst.compress a in
          uu____2525.FStar_Syntax_Syntax.n in
        (match uu____2524 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
             Some b
         | uu____2530 -> None) in
  let arg_as_char uu____2537 =
    match uu____2537 with
    | (a,uu____2542) ->
        let uu____2544 =
          let uu____2545 = FStar_Syntax_Subst.compress a in
          uu____2545.FStar_Syntax_Syntax.n in
        (match uu____2544 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
             Some c
         | uu____2550 -> None) in
  let arg_as_string uu____2557 =
    match uu____2557 with
    | (a,uu____2562) ->
        let uu____2564 =
          let uu____2565 = FStar_Syntax_Subst.compress a in
          uu____2565.FStar_Syntax_Syntax.n in
        (match uu____2564 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (bytes,uu____2570)) -> Some (FStar_Util.string_of_bytes bytes)
         | uu____2573 -> None) in
  let arg_as_list f uu____2594 =
    match uu____2594 with
    | (a,uu____2603) ->
        let rec sequence l =
          match l with
          | [] -> Some []
          | (None )::uu____2622 -> None
          | (Some x)::xs ->
              let uu____2632 = sequence xs in
              (match uu____2632 with
               | None  -> None
               | Some xs' -> Some (x :: xs')) in
        let uu____2643 = FStar_Syntax_Util.list_elements a in
        (match uu____2643 with
         | None  -> None
         | Some elts ->
             let uu____2653 =
               FStar_List.map
                 (fun x  ->
                    let uu____2658 = FStar_Syntax_Syntax.as_arg x in
                    f uu____2658) elts in
             sequence uu____2653) in
  let lift_unary f aopts =
    match aopts with
    | (Some a)::[] -> let uu____2688 = f a in Some uu____2688
    | uu____2689 -> None in
  let lift_binary f aopts =
    match aopts with
    | (Some a0)::(Some a1)::[] -> let uu____2728 = f a0 a1 in Some uu____2728
    | uu____2729 -> None in
  let unary_op as_a f r args =
    let uu____2773 = FStar_List.map as_a args in lift_unary (f r) uu____2773 in
  let binary_op as_a f r args =
    let uu____2823 = FStar_List.map as_a args in lift_binary (f r) uu____2823 in
  let as_primitive_step uu____2840 =
    match uu____2840 with
    | (l,arity,f) ->
        { name = l; arity; strong_reduction_ok = true; interpretation = f } in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  -> fun x  -> let uu____2878 = f x in int_as_const r uu____2878) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2901 = f x y in int_as_const r uu____2901) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  -> fun x  -> let uu____2918 = f x in bool_as_const r uu____2918) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2941 = f x y in bool_as_const r uu____2941) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2964 = f x y in string_as_const r uu____2964) in
  let list_of_string' rng s =
    let name l =
      let uu____2978 =
        let uu____2979 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            None in
        FStar_Syntax_Syntax.Tm_fvar uu____2979 in
      mk uu____2978 rng in
    let char_t = name FStar_Syntax_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____2989 =
      let uu____2991 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____2991 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____2989 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Const.exp_string s in
  let string_of_int1 rng i =
    let uu____3013 = FStar_Util.string_of_int i in
    string_as_const rng uu____3013 in
  let string_of_bool1 rng b =
    string_as_const rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____3029 = FStar_Util.string_of_int i in
    string_as_const rng uu____3029 in
  let string_of_bool2 rng b =
    string_as_const rng (if b then "true" else "false") in
  let basic_ops =
    let uu____3048 =
      let uu____3058 =
        let uu____3068 =
          let uu____3078 =
            let uu____3088 =
              let uu____3098 =
                let uu____3108 =
                  let uu____3118 =
                    let uu____3128 =
                      let uu____3138 =
                        let uu____3148 =
                          let uu____3158 =
                            let uu____3168 =
                              let uu____3178 =
                                let uu____3188 =
                                  let uu____3198 =
                                    let uu____3208 =
                                      let uu____3217 =
                                        FStar_Syntax_Const.p2l
                                          ["FStar";
                                          "String";
                                          "list_of_string"] in
                                      (uu____3217, (Prims.parse_int "1"),
                                        (unary_op arg_as_string
                                           list_of_string')) in
                                    let uu____3223 =
                                      let uu____3233 =
                                        let uu____3242 =
                                          FStar_Syntax_Const.p2l
                                            ["FStar";
                                            "String";
                                            "string_of_list"] in
                                        (uu____3242, (Prims.parse_int "1"),
                                          (unary_op (arg_as_list arg_as_char)
                                             string_of_list')) in
                                      [uu____3233] in
                                    uu____3208 :: uu____3223 in
                                  (FStar_Syntax_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_bool string_of_bool2))
                                    :: uu____3198 in
                                (FStar_Syntax_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (unary_op arg_as_int string_of_int2)) ::
                                  uu____3188 in
                              (FStar_Syntax_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____3178 in
                            (FStar_Syntax_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____3168 in
                          (FStar_Syntax_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____3158 in
                        (FStar_Syntax_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____3148 in
                      (FStar_Syntax_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____3138 in
                    (FStar_Syntax_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
                      :: uu____3128 in
                  (FStar_Syntax_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____3118 in
                (FStar_Syntax_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____3108 in
              (FStar_Syntax_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____3098 in
            (FStar_Syntax_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____3088 in
          (FStar_Syntax_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____3078 in
        (FStar_Syntax_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____3068 in
      (FStar_Syntax_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____3058 in
    (FStar_Syntax_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____3048 in
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
      let uu____3537 =
        let uu____3538 =
          let uu____3539 = FStar_Syntax_Syntax.as_arg c in [uu____3539] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____3538 in
      uu____3537 None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____3563 =
              let uu____3572 = FStar_Syntax_Const.p2l ["FStar"; m; "add"] in
              (uu____3572, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____3581  ->
                        fun uu____3582  ->
                          match (uu____3581, uu____3582) with
                          | ((int_to_t1,x),(uu____3593,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____3599 =
              let uu____3609 =
                let uu____3618 = FStar_Syntax_Const.p2l ["FStar"; m; "sub"] in
                (uu____3618, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____3627  ->
                          fun uu____3628  ->
                            match (uu____3627, uu____3628) with
                            | ((int_to_t1,x),(uu____3639,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____3645 =
                let uu____3655 =
                  let uu____3664 = FStar_Syntax_Const.p2l ["FStar"; m; "mul"] in
                  (uu____3664, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____3673  ->
                            fun uu____3674  ->
                              match (uu____3673, uu____3674) with
                              | ((int_to_t1,x),(uu____3685,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____3655] in
              uu____3609 :: uu____3645 in
            uu____3563 :: uu____3599)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_bool rng args =
    match args with
    | (_typ,uu____3751)::(a1,uu____3753)::(a2,uu____3755)::[] ->
        let uu____3784 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3784 with
         | FStar_Syntax_Util.Equal  ->
             let uu____3786 =
               mk
                 (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_bool true)) rng in
             Some uu____3786
         | FStar_Syntax_Util.NotEqual  ->
             let uu____3791 =
               mk
                 (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_bool false)) rng in
             Some uu____3791
         | uu____3796 -> None)
    | uu____3797 -> failwith "Unexpected number of arguments" in
  let interp_prop r args =
    match args with
    | (_typ,uu____3810)::(a1,uu____3812)::(a2,uu____3814)::[] ->
        let uu____3843 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3843 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___156_3847 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___156_3847.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___156_3847.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___156_3847.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___157_3854 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___157_3854.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___157_3854.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___157_3854.FStar_Syntax_Syntax.vars)
                })
         | uu____3859 -> None)
    | (_typ,uu____3861)::uu____3862::(a1,uu____3864)::(a2,uu____3866)::[] ->
        let uu____3903 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3903 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___156_3907 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___156_3907.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___156_3907.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___156_3907.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___157_3914 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___157_3914.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___157_3914.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___157_3914.FStar_Syntax_Syntax.vars)
                })
         | uu____3919 -> None)
    | uu____3920 -> failwith "Unexpected number of arguments" in
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
      let uu____3931 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops cfg.steps) in
      if uu____3931
      then tm
      else
        (let uu____3933 = FStar_Syntax_Util.head_and_args tm in
         match uu____3933 with
         | (head1,args) ->
             let uu____3959 =
               let uu____3960 = FStar_Syntax_Util.un_uinst head1 in
               uu____3960.FStar_Syntax_Syntax.n in
             (match uu____3959 with
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____3964 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps in
                  (match uu____3964 with
                   | None  -> tm
                   | Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then tm
                       else
                         (let uu____3976 =
                            prim_step.interpretation
                              head1.FStar_Syntax_Syntax.pos args in
                          match uu____3976 with
                          | None  -> tm
                          | Some reduced -> reduced))
              | uu____3979 -> tm))
let reduce_equality:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___158_3986 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___158_3986.tcenv);
           delta_level = (uu___158_3986.delta_level);
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
        let uu___159_4008 = t in
        {
          FStar_Syntax_Syntax.n = (uu___159_4008.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___159_4008.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___159_4008.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid ->
            Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid ->
            Some false
        | uu____4027 -> None in
      let simplify arg = ((simp_t (fst arg)), arg) in
      let uu____4054 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps) in
      if uu____4054
      then reduce_primops cfg tm
      else
        (match tm.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.tk = uu____4057;
                     FStar_Syntax_Syntax.pos = uu____4058;
                     FStar_Syntax_Syntax.vars = uu____4059;_},uu____4060);
                FStar_Syntax_Syntax.tk = uu____4061;
                FStar_Syntax_Syntax.pos = uu____4062;
                FStar_Syntax_Syntax.vars = uu____4063;_},args)
             ->
             let uu____4083 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____4083
             then
               let uu____4084 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____4084 with
                | (Some (true ),uu____4117)::(uu____4118,(arg,uu____4120))::[]
                    -> arg
                | (uu____4161,(arg,uu____4163))::(Some (true ),uu____4164)::[]
                    -> arg
                | (Some (false ),uu____4205)::uu____4206::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4244::(Some (false ),uu____4245)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4283 -> tm)
             else
               (let uu____4293 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____4293
                then
                  let uu____4294 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____4294 with
                  | (Some (true ),uu____4327)::uu____4328::[] ->
                      w FStar_Syntax_Util.t_true
                  | uu____4366::(Some (true ),uu____4367)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),uu____4405)::(uu____4406,(arg,uu____4408))::[]
                      -> arg
                  | (uu____4449,(arg,uu____4451))::(Some (false ),uu____4452)::[]
                      -> arg
                  | uu____4493 -> tm
                else
                  (let uu____4503 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____4503
                   then
                     let uu____4504 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____4504 with
                     | uu____4537::(Some (true ),uu____4538)::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (false ),uu____4576)::uu____4577::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____4615)::(uu____4616,(arg,uu____4618))::[]
                         -> arg
                     | uu____4659 -> tm
                   else
                     (let uu____4669 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____4669
                      then
                        let uu____4670 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____4670 with
                        | (Some (true ),uu____4703)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____4727)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____4751 -> tm
                      else
                        (let uu____4761 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid in
                         if uu____4761
                         then
                           match args with
                           | (t,uu____4763)::[] ->
                               let uu____4776 =
                                 let uu____4777 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____4777.FStar_Syntax_Syntax.n in
                               (match uu____4776 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____4780::[],body,uu____4782) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____4808 -> tm)
                                | uu____4810 -> tm)
                           | (uu____4811,Some (FStar_Syntax_Syntax.Implicit
                              uu____4812))::(t,uu____4814)::[] ->
                               let uu____4841 =
                                 let uu____4842 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____4842.FStar_Syntax_Syntax.n in
                               (match uu____4841 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____4845::[],body,uu____4847) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____4873 -> tm)
                                | uu____4875 -> tm)
                           | uu____4876 -> tm
                         else
                           (let uu____4883 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid in
                            if uu____4883
                            then
                              match args with
                              | (t,uu____4885)::[] ->
                                  let uu____4898 =
                                    let uu____4899 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____4899.FStar_Syntax_Syntax.n in
                                  (match uu____4898 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____4902::[],body,uu____4904) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____4930 -> tm)
                                   | uu____4932 -> tm)
                              | (uu____4933,Some
                                 (FStar_Syntax_Syntax.Implicit uu____4934))::
                                  (t,uu____4936)::[] ->
                                  let uu____4963 =
                                    let uu____4964 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____4964.FStar_Syntax_Syntax.n in
                                  (match uu____4963 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____4967::[],body,uu____4969) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____4995 -> tm)
                                   | uu____4997 -> tm)
                              | uu____4998 -> tm
                            else reduce_equality cfg tm)))))
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                FStar_Syntax_Syntax.tk = uu____5006;
                FStar_Syntax_Syntax.pos = uu____5007;
                FStar_Syntax_Syntax.vars = uu____5008;_},args)
             ->
             let uu____5024 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____5024
             then
               let uu____5025 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____5025 with
                | (Some (true ),uu____5058)::(uu____5059,(arg,uu____5061))::[]
                    -> arg
                | (uu____5102,(arg,uu____5104))::(Some (true ),uu____5105)::[]
                    -> arg
                | (Some (false ),uu____5146)::uu____5147::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____5185::(Some (false ),uu____5186)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____5224 -> tm)
             else
               (let uu____5234 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____5234
                then
                  let uu____5235 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____5235 with
                  | (Some (true ),uu____5268)::uu____5269::[] ->
                      w FStar_Syntax_Util.t_true
                  | uu____5307::(Some (true ),uu____5308)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),uu____5346)::(uu____5347,(arg,uu____5349))::[]
                      -> arg
                  | (uu____5390,(arg,uu____5392))::(Some (false ),uu____5393)::[]
                      -> arg
                  | uu____5434 -> tm
                else
                  (let uu____5444 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____5444
                   then
                     let uu____5445 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____5445 with
                     | uu____5478::(Some (true ),uu____5479)::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (false ),uu____5517)::uu____5518::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____5556)::(uu____5557,(arg,uu____5559))::[]
                         -> arg
                     | uu____5600 -> tm
                   else
                     (let uu____5610 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____5610
                      then
                        let uu____5611 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____5611 with
                        | (Some (true ),uu____5644)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____5668)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____5692 -> tm
                      else
                        (let uu____5702 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid in
                         if uu____5702
                         then
                           match args with
                           | (t,uu____5704)::[] ->
                               let uu____5717 =
                                 let uu____5718 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5718.FStar_Syntax_Syntax.n in
                               (match uu____5717 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5721::[],body,uu____5723) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5749 -> tm)
                                | uu____5751 -> tm)
                           | (uu____5752,Some (FStar_Syntax_Syntax.Implicit
                              uu____5753))::(t,uu____5755)::[] ->
                               let uu____5782 =
                                 let uu____5783 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5783.FStar_Syntax_Syntax.n in
                               (match uu____5782 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5786::[],body,uu____5788) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5814 -> tm)
                                | uu____5816 -> tm)
                           | uu____5817 -> tm
                         else
                           (let uu____5824 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid in
                            if uu____5824
                            then
                              match args with
                              | (t,uu____5826)::[] ->
                                  let uu____5839 =
                                    let uu____5840 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5840.FStar_Syntax_Syntax.n in
                                  (match uu____5839 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5843::[],body,uu____5845) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5871 -> tm)
                                   | uu____5873 -> tm)
                              | (uu____5874,Some
                                 (FStar_Syntax_Syntax.Implicit uu____5875))::
                                  (t,uu____5877)::[] ->
                                  let uu____5904 =
                                    let uu____5905 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5905.FStar_Syntax_Syntax.n in
                                  (match uu____5904 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5908::[],body,uu____5910) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5936 -> tm)
                                   | uu____5938 -> tm)
                              | uu____5939 -> tm
                            else reduce_equality cfg tm)))))
         | uu____5946 -> tm)
let is_norm_request hd1 args =
  let uu____5961 =
    let uu____5965 =
      let uu____5966 = FStar_Syntax_Util.un_uinst hd1 in
      uu____5966.FStar_Syntax_Syntax.n in
    (uu____5965, args) in
  match uu____5961 with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5971::uu____5972::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize_term
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5975::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize
  | uu____5977 -> false
let get_norm_request args =
  match args with
  | uu____5996::(tm,uu____5998)::[] -> tm
  | (tm,uu____6008)::[] -> tm
  | uu____6013 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___135_6020  ->
    match uu___135_6020 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.tk = uu____6022;
           FStar_Syntax_Syntax.pos = uu____6023;
           FStar_Syntax_Syntax.vars = uu____6024;_},uu____6025,uu____6026))::uu____6027
        -> true
    | uu____6033 -> false
let is_fstar_tactics_embed: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____6038 =
      let uu____6039 = FStar_Syntax_Util.un_uinst t in
      uu____6039.FStar_Syntax_Syntax.n in
    match uu____6038 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Syntax_Const.fstar_tactics_embed_lid
    | uu____6043 -> false
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
            (fun uu____6157  ->
               let uu____6158 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____6159 = FStar_Syntax_Print.term_to_string t1 in
               let uu____6160 =
                 let uu____6161 =
                   let uu____6163 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives.fst uu____6163 in
                 stack_to_string uu____6161 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____6158
                 uu____6159 uu____6160);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____6175 ->
               failwith "Impossible"
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____6196 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____6205 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____6206 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6207;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____6208;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6213;
                 FStar_Syntax_Syntax.fv_delta = uu____6214;
                 FStar_Syntax_Syntax.fv_qual = Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6218;
                 FStar_Syntax_Syntax.fv_delta = uu____6219;
                 FStar_Syntax_Syntax.fv_qual = Some
                   (FStar_Syntax_Syntax.Record_ctor uu____6220);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.tk = uu____6228;
                  FStar_Syntax_Syntax.pos = uu____6229;
                  FStar_Syntax_Syntax.vars = uu____6230;_},uu____6231)
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Syntax_Const.fstar_tactics_embed_lid
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               is_fstar_tactics_embed hd1 ->
               let args1 = closures_as_args_delayed cfg env args in
               let t2 =
                 let uu___160_6271 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd1, args1));
                   FStar_Syntax_Syntax.tk =
                     (uu___160_6271.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___160_6271.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___160_6271.FStar_Syntax_Syntax.vars)
                 } in
               let t3 = reduce_primops cfg t2 in rebuild cfg env stack1 t3
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____6300 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____6300) && (is_norm_request hd1 args))
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
                 let uu___161_6313 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___161_6313.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___161_6313.primitive_steps)
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
                  FStar_Syntax_Syntax.tk = uu____6318;
                  FStar_Syntax_Syntax.pos = uu____6319;
                  FStar_Syntax_Syntax.vars = uu____6320;_},a1::a2::rest)
               ->
               let uu____6354 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6354 with
                | (hd1,uu____6365) ->
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
                    (FStar_Const.Const_reflect uu____6420);
                  FStar_Syntax_Syntax.tk = uu____6421;
                  FStar_Syntax_Syntax.pos = uu____6422;
                  FStar_Syntax_Syntax.vars = uu____6423;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____6446 = FStar_List.tl stack1 in
               norm cfg env uu____6446 (fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.tk = uu____6449;
                  FStar_Syntax_Syntax.pos = uu____6450;
                  FStar_Syntax_Syntax.vars = uu____6451;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____6474 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6474 with
                | (reify_head,uu____6485) ->
                    let a1 =
                      let uu____6501 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (fst a) in
                      FStar_Syntax_Subst.compress uu____6501 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____6504);
                            FStar_Syntax_Syntax.tk = uu____6505;
                            FStar_Syntax_Syntax.pos = uu____6506;
                            FStar_Syntax_Syntax.vars = uu____6507;_},a2::[])
                         -> norm cfg env stack1 (fst a2)
                     | uu____6532 ->
                         let stack2 =
                           (App
                              (reify_head, None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____6540 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____6540
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____6547 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____6547
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____6550 =
                      let uu____6554 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____6554, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____6550 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___136_6563  ->
                         match uu___136_6563 with
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
                    let uu____6567 = FStar_Syntax_Syntax.range_of_fv f in
                    FStar_TypeChecker_Env.set_range cfg.tcenv uu____6567 in
                  let uu____6568 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  match uu____6568 with
                  | None  ->
                      (log cfg
                         (fun uu____6579  ->
                            FStar_Util.print "Tm_fvar case 2\n" []);
                       rebuild cfg env stack1 t1)
                  | Some (us,t2) ->
                      (log cfg
                         (fun uu____6585  ->
                            let uu____6586 =
                              FStar_Syntax_Print.term_to_string t0 in
                            let uu____6587 =
                              FStar_Syntax_Print.term_to_string t2 in
                            FStar_Util.print2 ">>> Unfolded %s to %s\n"
                              uu____6586 uu____6587);
                       (let t3 =
                          let uu____6589 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 (UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant)) in
                          if uu____6589
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
                          | (UnivArgs (us',uu____6601))::stack2 ->
                              let env1 =
                                FStar_All.pipe_right us'
                                  (FStar_List.fold_left
                                     (fun env1  -> fun u  -> (Univ u) :: env1)
                                     env) in
                              norm cfg env1 stack2 t3
                          | uu____6614 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack1 t3
                          | uu____6615 ->
                              let uu____6616 =
                                let uu____6617 =
                                  FStar_Syntax_Print.lid_to_string
                                    (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                FStar_Util.format1
                                  "Impossible: missing universe instantiation on %s"
                                  uu____6617 in
                              failwith uu____6616
                        else norm cfg env stack1 t3)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____6624 = lookup_bvar env x in
               (match uu____6624 with
                | Univ uu____6625 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____6640 = FStar_ST.read r in
                      (match uu____6640 with
                       | Some (env2,t') ->
                           (log cfg
                              (fun uu____6659  ->
                                 let uu____6660 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____6661 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____6660
                                   uu____6661);
                            (let uu____6662 =
                               let uu____6663 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____6663.FStar_Syntax_Syntax.n in
                             match uu____6662 with
                             | FStar_Syntax_Syntax.Tm_abs uu____6666 ->
                                 norm cfg env2 stack1 t'
                             | uu____6681 -> rebuild cfg env2 stack1 t'))
                       | None  -> norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____6714)::uu____6715 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____6720)::uu____6721 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____6727,uu____6728))::stack_rest ->
                    (match c with
                     | Univ uu____6731 -> norm cfg (c :: env) stack_rest t1
                     | uu____6732 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____6735::[] ->
                              (match lopt with
                               | None  when FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____6748  ->
                                         let uu____6749 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6749);
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
                                           (fun uu___137_6763  ->
                                              match uu___137_6763 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____6764 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____6766  ->
                                         let uu____6767 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6767);
                                    norm cfg (c :: env) stack_rest body)
                               | Some (FStar_Util.Inl lc) when
                                   FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                                   ->
                                   (log cfg
                                      (fun uu____6778  ->
                                         let uu____6779 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6779);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____6780 when
                                   FStar_All.pipe_right cfg.steps
                                     (FStar_List.contains Reify)
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____6787 ->
                                   let cfg1 =
                                     let uu___162_6795 = cfg in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___162_6795.tcenv);
                                       delta_level =
                                         (uu___162_6795.delta_level);
                                       primitive_steps =
                                         (uu___162_6795.primitive_steps)
                                     } in
                                   let uu____6796 =
                                     closure_as_term cfg1 env t1 in
                                   rebuild cfg1 env stack1 uu____6796)
                          | uu____6797::tl1 ->
                              (log cfg
                                 (fun uu____6807  ->
                                    let uu____6808 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____6808);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___163_6832 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___163_6832.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____6845  ->
                          let uu____6846 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____6846);
                     norm cfg env stack2 t1)
                | (Debug uu____6847)::uu____6848 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____6850 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____6850
                    else
                      (let uu____6852 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____6852 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____6881 =
                                   let uu____6887 =
                                     let uu____6888 =
                                       let uu____6889 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____6889 in
                                     FStar_All.pipe_right uu____6888
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____6887
                                     (fun _0_31  -> FStar_Util.Inl _0_31) in
                                 FStar_All.pipe_right uu____6881
                                   (fun _0_32  -> Some _0_32)
                             | uu____6914 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____6928  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____6933  ->
                                 let uu____6934 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____6934);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___164_6944 = cfg in
                               let uu____6945 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___164_6944.steps);
                                 tcenv = (uu___164_6944.tcenv);
                                 delta_level = (uu___164_6944.delta_level);
                                 primitive_steps = uu____6945
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____6955)::uu____6956 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____6960 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____6960
                    else
                      (let uu____6962 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____6962 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____6991 =
                                   let uu____6997 =
                                     let uu____6998 =
                                       let uu____6999 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____6999 in
                                     FStar_All.pipe_right uu____6998
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____6997
                                     (fun _0_33  -> FStar_Util.Inl _0_33) in
                                 FStar_All.pipe_right uu____6991
                                   (fun _0_34  -> Some _0_34)
                             | uu____7024 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7038  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7043  ->
                                 let uu____7044 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7044);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___164_7054 = cfg in
                               let uu____7055 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___164_7054.steps);
                                 tcenv = (uu___164_7054.tcenv);
                                 delta_level = (uu___164_7054.delta_level);
                                 primitive_steps = uu____7055
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____7065)::uu____7066 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7072 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7072
                    else
                      (let uu____7074 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7074 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7103 =
                                   let uu____7109 =
                                     let uu____7110 =
                                       let uu____7111 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7111 in
                                     FStar_All.pipe_right uu____7110
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7109
                                     (fun _0_35  -> FStar_Util.Inl _0_35) in
                                 FStar_All.pipe_right uu____7103
                                   (fun _0_36  -> Some _0_36)
                             | uu____7136 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7150  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7155  ->
                                 let uu____7156 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7156);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___164_7166 = cfg in
                               let uu____7167 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___164_7166.steps);
                                 tcenv = (uu___164_7166.tcenv);
                                 delta_level = (uu___164_7166.delta_level);
                                 primitive_steps = uu____7167
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____7177)::uu____7178 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7183 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7183
                    else
                      (let uu____7185 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7185 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7214 =
                                   let uu____7220 =
                                     let uu____7221 =
                                       let uu____7222 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7222 in
                                     FStar_All.pipe_right uu____7221
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7220
                                     (fun _0_37  -> FStar_Util.Inl _0_37) in
                                 FStar_All.pipe_right uu____7214
                                   (fun _0_38  -> Some _0_38)
                             | uu____7247 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7261  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7266  ->
                                 let uu____7267 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7267);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___164_7277 = cfg in
                               let uu____7278 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___164_7277.steps);
                                 tcenv = (uu___164_7277.tcenv);
                                 delta_level = (uu___164_7277.delta_level);
                                 primitive_steps = uu____7278
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____7288)::uu____7289 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7299 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7299
                    else
                      (let uu____7301 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7301 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7330 =
                                   let uu____7336 =
                                     let uu____7337 =
                                       let uu____7338 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7338 in
                                     FStar_All.pipe_right uu____7337
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7336
                                     (fun _0_39  -> FStar_Util.Inl _0_39) in
                                 FStar_All.pipe_right uu____7330
                                   (fun _0_40  -> Some _0_40)
                             | uu____7363 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7377  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7382  ->
                                 let uu____7383 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7383);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___164_7393 = cfg in
                               let uu____7394 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___164_7393.steps);
                                 tcenv = (uu___164_7393.tcenv);
                                 delta_level = (uu___164_7393.delta_level);
                                 primitive_steps = uu____7394
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7404 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7404
                    else
                      (let uu____7406 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7406 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7435 =
                                   let uu____7441 =
                                     let uu____7442 =
                                       let uu____7443 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7443 in
                                     FStar_All.pipe_right uu____7442
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7441
                                     (fun _0_41  -> FStar_Util.Inl _0_41) in
                                 FStar_All.pipe_right uu____7435
                                   (fun _0_42  -> Some _0_42)
                             | uu____7468 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7482  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7487  ->
                                 let uu____7488 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7488);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___164_7498 = cfg in
                               let uu____7499 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___164_7498.steps);
                                 tcenv = (uu___164_7498.tcenv);
                                 delta_level = (uu___164_7498.delta_level);
                                 primitive_steps = uu____7499
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
                      (fun uu____7531  ->
                         fun stack2  ->
                           match uu____7531 with
                           | (a,aq) ->
                               let uu____7539 =
                                 let uu____7540 =
                                   let uu____7544 =
                                     let uu____7545 =
                                       let uu____7555 =
                                         FStar_Util.mk_ref None in
                                       (env, a, uu____7555, false) in
                                     Clos uu____7545 in
                                   (uu____7544, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____7540 in
                               uu____7539 :: stack2) args) in
               (log cfg
                  (fun uu____7577  ->
                     let uu____7578 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____7578);
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
                             ((let uu___165_7599 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___165_7599.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___165_7599.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____7600 ->
                      let uu____7603 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7603)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____7606 = FStar_Syntax_Subst.open_term [(x, None)] f in
                  match uu____7606 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____7622 =
                          let uu____7623 =
                            let uu____7628 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___166_7629 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___166_7629.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___166_7629.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____7628) in
                          FStar_Syntax_Syntax.Tm_refine uu____7623 in
                        mk uu____7622 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____7642 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____7642
               else
                 (let uu____7644 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____7644 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____7650 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  -> fun uu____7656  -> Dummy :: env1)
                               env) in
                        norm_comp cfg uu____7650 c1 in
                      let t2 =
                        let uu____7663 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____7663 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____7706)::uu____7707 -> norm cfg env stack1 t11
                | (Arg uu____7712)::uu____7713 -> norm cfg env stack1 t11
                | (App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.tk = uu____7718;
                       FStar_Syntax_Syntax.pos = uu____7719;
                       FStar_Syntax_Syntax.vars = uu____7720;_},uu____7721,uu____7722))::uu____7723
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____7729)::uu____7730 ->
                    norm cfg env stack1 t11
                | uu____7735 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____7738  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____7751 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____7751
                        | FStar_Util.Inr c ->
                            let uu____7759 = norm_comp cfg env c in
                            FStar_Util.Inr uu____7759 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____7764 =
                        mk
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (t12, (tc1, tacopt1), l))
                          t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____7764)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____7815,{
                              FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                uu____7816;
                              FStar_Syntax_Syntax.lbunivs = uu____7817;
                              FStar_Syntax_Syntax.lbtyp = uu____7818;
                              FStar_Syntax_Syntax.lbeff = uu____7819;
                              FStar_Syntax_Syntax.lbdef = uu____7820;_}::uu____7821),uu____7822)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____7848 =
                 (let uu____7849 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____7849) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____7850 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____7850))) in
               if uu____7848
               then
                 let env1 =
                   let uu____7853 =
                     let uu____7854 =
                       let uu____7864 = FStar_Util.mk_ref None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____7864,
                         false) in
                     Clos uu____7854 in
                   uu____7853 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____7888 =
                    let uu____7891 =
                      let uu____7892 =
                        let uu____7893 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____7893
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____7892] in
                    FStar_Syntax_Subst.open_term uu____7891 body in
                  match uu____7888 with
                  | (bs,body1) ->
                      let lb1 =
                        let uu___167_7899 = lb in
                        let uu____7900 =
                          let uu____7903 =
                            let uu____7904 = FStar_List.hd bs in
                            FStar_All.pipe_right uu____7904
                              FStar_Pervasives.fst in
                          FStar_All.pipe_right uu____7903
                            (fun _0_43  -> FStar_Util.Inl _0_43) in
                        let uu____7913 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____7916 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = uu____7900;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___167_7899.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____7913;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___167_7899.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____7916
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____7926  -> Dummy :: env1)
                             env) in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____7942 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____7942
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____7955 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____7977  ->
                        match uu____7977 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____8016 =
                                let uu___168_8017 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___168_8017.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___168_8017.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____8016 in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos in
                            let memo = FStar_Util.mk_ref None in
                            let rec_env1 = (Clos (env, fix_f_i, memo, true))
                              :: rec_env in
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1")))) (snd lbs)
                   (env, [], (Prims.parse_int "0")) in
               (match uu____7955 with
                | (rec_env,memos,uu____8077) ->
                    let uu____8092 =
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
                             let uu____8134 =
                               let uu____8135 =
                                 let uu____8145 = FStar_Util.mk_ref None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____8145, false) in
                               Clos uu____8135 in
                             uu____8134 :: env1) (snd lbs) env in
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
                             FStar_Syntax_Syntax.tk = uu____8183;
                             FStar_Syntax_Syntax.pos = uu____8184;
                             FStar_Syntax_Syntax.vars = uu____8185;_},uu____8186,uu____8187))::uu____8188
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____8194 -> false in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____8201 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____8201
                        then
                          let uu___169_8202 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___169_8202.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps = (uu___169_8202.primitive_steps)
                          }
                        else
                          (let uu___170_8204 = cfg in
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___170_8204.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta];
                             primitive_steps =
                               (uu___170_8204.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____8206 =
                         let uu____8207 = FStar_Syntax_Subst.compress head1 in
                         uu____8207.FStar_Syntax_Syntax.n in
                       match uu____8206 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____8221 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8221 with
                            | (uu____8222,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____8226 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____8233 =
                                         let uu____8234 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____8234.FStar_Syntax_Syntax.n in
                                       match uu____8233 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____8239,uu____8240))
                                           ->
                                           let uu____8249 =
                                             let uu____8250 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____8250.FStar_Syntax_Syntax.n in
                                           (match uu____8249 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____8255,msrc,uu____8257))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____8266 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                Some uu____8266
                                            | uu____8267 -> None)
                                       | uu____8268 -> None in
                                     let uu____8269 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____8269 with
                                      | Some e ->
                                          let lb1 =
                                            let uu___171_8273 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___171_8273.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___171_8273.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___171_8273.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Syntax_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____8274 =
                                            FStar_List.tl stack1 in
                                          let uu____8275 =
                                            let uu____8276 =
                                              let uu____8279 =
                                                let uu____8280 =
                                                  let uu____8288 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____8288) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____8280 in
                                              FStar_Syntax_Syntax.mk
                                                uu____8279 in
                                            uu____8276 None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____8274 uu____8275
                                      | None  ->
                                          let uu____8305 =
                                            let uu____8306 = is_return body in
                                            match uu____8306 with
                                            | Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____8309;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____8310;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____8311;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____8316 -> false in
                                          if uu____8305
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
                                               let uu____8336 =
                                                 let uu____8339 =
                                                   let uu____8340 =
                                                     let uu____8355 =
                                                       let uu____8357 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____8357] in
                                                     (uu____8355, body1,
                                                       (Some
                                                          (FStar_Util.Inr
                                                             (m1, [])))) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____8340 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8339 in
                                               uu____8336 None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____8390 =
                                                 let uu____8391 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____8391.FStar_Syntax_Syntax.n in
                                               match uu____8390 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____8397::uu____8398::[])
                                                   ->
                                                   let uu____8404 =
                                                     let uu____8407 =
                                                       let uu____8408 =
                                                         let uu____8413 =
                                                           let uu____8415 =
                                                             let uu____8416 =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____8416 in
                                                           let uu____8417 =
                                                             let uu____8419 =
                                                               let uu____8420
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____8420 in
                                                             [uu____8419] in
                                                           uu____8415 ::
                                                             uu____8417 in
                                                         (bind1, uu____8413) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____8408 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8407 in
                                                   uu____8404 None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____8432 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____8438 =
                                                 let uu____8441 =
                                                   let uu____8442 =
                                                     let uu____8452 =
                                                       let uu____8454 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____8455 =
                                                         let uu____8457 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____8458 =
                                                           let uu____8460 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____8461 =
                                                             let uu____8463 =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____8464 =
                                                               let uu____8466
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____8467
                                                                 =
                                                                 let uu____8469
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____8469] in
                                                               uu____8466 ::
                                                                 uu____8467 in
                                                             uu____8463 ::
                                                               uu____8464 in
                                                           uu____8460 ::
                                                             uu____8461 in
                                                         uu____8457 ::
                                                           uu____8458 in
                                                       uu____8454 ::
                                                         uu____8455 in
                                                     (bind_inst, uu____8452) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____8442 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8441 in
                                               uu____8438 None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____8481 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____8481 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____8499 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8499 with
                            | (uu____8500,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____8523 =
                                        let uu____8524 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____8524.FStar_Syntax_Syntax.n in
                                      match uu____8523 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____8530) -> t4
                                      | uu____8535 -> head2 in
                                    let uu____8536 =
                                      let uu____8537 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____8537.FStar_Syntax_Syntax.n in
                                    match uu____8536 with
                                    | FStar_Syntax_Syntax.Tm_fvar x -> Some x
                                    | uu____8542 -> None in
                                  let uu____8543 = maybe_extract_fv head2 in
                                  match uu____8543 with
                                  | Some x when
                                      let uu____8549 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____8549
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____8553 =
                                          maybe_extract_fv head3 in
                                        match uu____8553 with
                                        | Some uu____8556 -> Some true
                                        | uu____8557 -> Some false in
                                      (head3, action_unfolded)
                                  | uu____8560 -> (head2, None) in
                                ((let is_arg_impure uu____8571 =
                                    match uu____8571 with
                                    | (e,q) ->
                                        let uu____8576 =
                                          let uu____8577 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____8577.FStar_Syntax_Syntax.n in
                                        (match uu____8576 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____8592 -> false) in
                                  let uu____8593 =
                                    let uu____8594 =
                                      let uu____8598 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____8598 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____8594 in
                                  if uu____8593
                                  then
                                    let uu____8601 =
                                      let uu____8602 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____8602 in
                                    failwith uu____8601
                                  else ());
                                 (let uu____8604 =
                                    maybe_unfold_action head_app in
                                  match uu____8604 with
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
                                      let uu____8639 = FStar_List.tl stack1 in
                                      norm cfg env uu____8639 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____8653 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____8653 in
                           let uu____8654 = FStar_List.tl stack1 in
                           norm cfg env uu____8654 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____8737  ->
                                     match uu____8737 with
                                     | (pat,wopt,tm) ->
                                         let uu____8775 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____8775))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____8801 = FStar_List.tl stack1 in
                           norm cfg env uu____8801 tm
                       | uu____8802 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.tk = uu____8811;
                             FStar_Syntax_Syntax.pos = uu____8812;
                             FStar_Syntax_Syntax.vars = uu____8813;_},uu____8814,uu____8815))::uu____8816
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____8822 -> false in
                    if should_reify
                    then
                      let uu____8823 = FStar_List.tl stack1 in
                      let uu____8824 =
                        let uu____8825 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____8825 in
                      norm cfg env uu____8823 uu____8824
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____8828 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____8828
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___172_8834 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___172_8834.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___172_8834.primitive_steps)
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
                | uu____8836 ->
                    (match stack1 with
                     | uu____8837::uu____8838 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____8842)
                              -> norm cfg env ((Meta (m, r)) :: stack1) head1
                          | FStar_Syntax_Syntax.Meta_pattern args ->
                              let args1 = norm_pattern_args cfg env args in
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_pattern args1),
                                      (t1.FStar_Syntax_Syntax.pos))) ::
                                stack1) head1
                          | uu____8857 -> norm cfg env stack1 head1)
                     | [] ->
                         let head2 = norm cfg env [] head1 in
                         let m1 =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               let uu____8867 =
                                 norm_pattern_args cfg env args in
                               FStar_Syntax_Syntax.Meta_pattern uu____8867
                           | uu____8874 -> m in
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
              let uu____8886 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____8886 with
              | (uu____8887,return_repr) ->
                  let return_inst =
                    let uu____8894 =
                      let uu____8895 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____8895.FStar_Syntax_Syntax.n in
                    match uu____8894 with
                    | FStar_Syntax_Syntax.Tm_uinst (return_tm,uu____8901::[])
                        ->
                        let uu____8907 =
                          let uu____8910 =
                            let uu____8911 =
                              let uu____8916 =
                                let uu____8918 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____8918] in
                              (return_tm, uu____8916) in
                            FStar_Syntax_Syntax.Tm_uinst uu____8911 in
                          FStar_Syntax_Syntax.mk uu____8910 in
                        uu____8907 None e.FStar_Syntax_Syntax.pos
                    | uu____8930 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____8933 =
                    let uu____8936 =
                      let uu____8937 =
                        let uu____8947 =
                          let uu____8949 = FStar_Syntax_Syntax.as_arg t in
                          let uu____8950 =
                            let uu____8952 = FStar_Syntax_Syntax.as_arg e in
                            [uu____8952] in
                          uu____8949 :: uu____8950 in
                        (return_inst, uu____8947) in
                      FStar_Syntax_Syntax.Tm_app uu____8937 in
                    FStar_Syntax_Syntax.mk uu____8936 in
                  uu____8933 None e.FStar_Syntax_Syntax.pos
            else
              (let uu____8965 = FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____8965 with
               | None  ->
                   let uu____8967 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____8967
               | Some
                   { FStar_TypeChecker_Env.msource = uu____8968;
                     FStar_TypeChecker_Env.mtarget = uu____8969;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____8970;
                         FStar_TypeChecker_Env.mlift_term = None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | Some
                   { FStar_TypeChecker_Env.msource = uu____8981;
                     FStar_TypeChecker_Env.mtarget = uu____8982;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____8983;
                         FStar_TypeChecker_Env.mlift_term = Some lift;_};_}
                   ->
                   let uu____9001 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____9001)
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
                (fun uu____9031  ->
                   match uu____9031 with
                   | (a,imp) ->
                       let uu____9038 = norm cfg env [] a in
                       (uu____9038, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___173_9053 = comp1 in
            let uu____9056 =
              let uu____9057 =
                let uu____9063 = norm cfg env [] t in
                let uu____9064 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____9063, uu____9064) in
              FStar_Syntax_Syntax.Total uu____9057 in
            {
              FStar_Syntax_Syntax.n = uu____9056;
              FStar_Syntax_Syntax.tk = (uu___173_9053.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___173_9053.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___173_9053.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___174_9079 = comp1 in
            let uu____9082 =
              let uu____9083 =
                let uu____9089 = norm cfg env [] t in
                let uu____9090 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____9089, uu____9090) in
              FStar_Syntax_Syntax.GTotal uu____9083 in
            {
              FStar_Syntax_Syntax.n = uu____9082;
              FStar_Syntax_Syntax.tk = (uu___174_9079.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___174_9079.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___174_9079.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____9121  ->
                      match uu____9121 with
                      | (a,i) ->
                          let uu____9128 = norm cfg env [] a in
                          (uu____9128, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___138_9133  ->
                      match uu___138_9133 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____9137 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____9137
                      | f -> f)) in
            let uu___175_9141 = comp1 in
            let uu____9144 =
              let uu____9145 =
                let uu___176_9146 = ct in
                let uu____9147 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____9148 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____9151 = norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____9147;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___176_9146.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____9148;
                  FStar_Syntax_Syntax.effect_args = uu____9151;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____9145 in
            {
              FStar_Syntax_Syntax.n = uu____9144;
              FStar_Syntax_Syntax.tk = (uu___175_9141.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___175_9141.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___175_9141.FStar_Syntax_Syntax.vars)
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
            (let uu___177_9168 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___177_9168.tcenv);
               delta_level = (uu___177_9168.delta_level);
               primitive_steps = (uu___177_9168.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____9173 = norm1 t in
          FStar_Syntax_Util.non_informative uu____9173 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____9176 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___178_9190 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.tk = (uu___178_9190.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___178_9190.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___178_9190.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____9200 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____9200
            then
              let ct1 =
                match downgrade_ghost_effect_name
                        ct.FStar_Syntax_Syntax.effect_name
                with
                | Some pure_eff ->
                    let uu___179_9205 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___179_9205.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___179_9205.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___179_9205.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___179_9205.FStar_Syntax_Syntax.flags)
                    }
                | None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___180_9207 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___180_9207.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Syntax_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___180_9207.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___180_9207.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___180_9207.FStar_Syntax_Syntax.flags)
                    } in
              let uu___181_9208 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.tk =
                  (uu___181_9208.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___181_9208.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___181_9208.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____9214 -> c
and norm_binder:
  cfg ->
    env ->
      FStar_Syntax_Syntax.binder ->
        (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  =
  fun cfg  ->
    fun env  ->
      fun uu____9217  ->
        match uu____9217 with
        | (x,imp) ->
            let uu____9220 =
              let uu___182_9221 = x in
              let uu____9222 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___182_9221.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___182_9221.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____9222
              } in
            (uu____9220, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____9228 =
          FStar_List.fold_left
            (fun uu____9235  ->
               fun b  ->
                 match uu____9235 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____9228 with | (nbs,uu____9252) -> FStar_List.rev nbs
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
            let uu____9269 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
            if uu____9269
            then
              let t = norm cfg env [] lc.FStar_Syntax_Syntax.res_typ in
              let uu____9274 = FStar_Syntax_Util.is_total_lcomp lc in
              (if uu____9274
               then
                 let uu____9278 =
                   let uu____9281 =
                     let uu____9282 =
                       let uu____9285 = FStar_Syntax_Syntax.mk_Total t in
                       FStar_Syntax_Util.comp_set_flags uu____9285 flags in
                     FStar_Syntax_Util.lcomp_of_comp uu____9282 in
                   FStar_Util.Inl uu____9281 in
                 Some uu____9278
               else
                 (let uu____9289 =
                    let uu____9292 =
                      let uu____9293 =
                        let uu____9296 = FStar_Syntax_Syntax.mk_GTotal t in
                        FStar_Syntax_Util.comp_set_flags uu____9296 flags in
                      FStar_Syntax_Util.lcomp_of_comp uu____9293 in
                    FStar_Util.Inl uu____9292 in
                  Some uu____9289))
            else
              Some
                (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags))
        | uu____9309 -> lopt
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
              ((let uu____9321 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____9321
                then
                  let uu____9322 = FStar_Syntax_Print.term_to_string tm in
                  let uu____9323 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2 "Normalized %s to %s\n" uu____9322
                    uu____9323
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___183_9334 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___183_9334.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____9354  ->
                    let uu____9355 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____9355);
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
              let uu____9392 =
                let uu___184_9393 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___184_9393.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___184_9393.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___184_9393.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____9392
          | (Arg (Univ uu____9398,uu____9399,uu____9400))::uu____9401 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____9403,uu____9404))::uu____9405 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____9417),aq,r))::stack2 ->
              (log cfg
                 (fun uu____9433  ->
                    let uu____9434 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____9434);
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
                 (let uu____9445 = FStar_ST.read m in
                  match uu____9445 with
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
                  | Some (uu____9471,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq) None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.extend_app head1 (t, aq) None r in
              let uu____9493 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____9493
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____9500  ->
                    let uu____9501 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____9501);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____9506 =
                  log cfg
                    (fun uu____9508  ->
                       let uu____9509 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____9510 =
                         let uu____9511 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____9518  ->
                                   match uu____9518 with
                                   | (p,uu____9524,uu____9525) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____9511
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____9509 uu____9510);
                  (let whnf = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___139_9535  ->
                               match uu___139_9535 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____9536 -> false)) in
                     let steps' =
                       let uu____9539 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____9539
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___185_9542 = cfg in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___185_9542.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___185_9542.primitive_steps)
                     } in
                   let norm_or_whnf env2 t1 =
                     if whnf
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____9576 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____9592 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____9626  ->
                                   fun uu____9627  ->
                                     match (uu____9626, uu____9627) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____9692 = norm_pat env3 p1 in
                                         (match uu____9692 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____9592 with
                          | (pats1,env3) ->
                              ((let uu___186_9758 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___186_9758.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___186_9758.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___187_9772 = x in
                           let uu____9773 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___187_9772.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___187_9772.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9773
                           } in
                         ((let uu___188_9779 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___188_9779.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___188_9779.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___189_9784 = x in
                           let uu____9785 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___189_9784.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___189_9784.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9785
                           } in
                         ((let uu___190_9791 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___190_9791.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___190_9791.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___191_9801 = x in
                           let uu____9802 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___191_9801.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___191_9801.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9802
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___192_9809 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.ty =
                               (uu___192_9809.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___192_9809.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf -> branches
                     | uu____9813 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____9816 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____9816 with
                                 | (p,wopt,e) ->
                                     let uu____9834 = norm_pat env1 p in
                                     (match uu____9834 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | None  -> None
                                            | Some w ->
                                                let uu____9858 =
                                                  norm_or_whnf env2 w in
                                                Some uu____9858 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____9863 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____9863) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____9873) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____9878 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____9879;
                        FStar_Syntax_Syntax.fv_delta = uu____9880;
                        FStar_Syntax_Syntax.fv_qual = Some
                          (FStar_Syntax_Syntax.Data_ctor );_}
                      -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____9884;
                        FStar_Syntax_Syntax.fv_delta = uu____9885;
                        FStar_Syntax_Syntax.fv_qual = Some
                          (FStar_Syntax_Syntax.Record_ctor uu____9886);_}
                      -> true
                  | uu____9893 -> false in
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
                  let uu____9992 = FStar_Syntax_Util.head_and_args scrutinee2 in
                  match uu____9992 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var uu____10024 ->
                           FStar_Util.Inl [scrutinee2]
                       | FStar_Syntax_Syntax.Pat_wild uu____10026 ->
                           FStar_Util.Inl [scrutinee2]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____10028 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____10040 ->
                                let uu____10041 =
                                  let uu____10042 = is_cons head1 in
                                  Prims.op_Negation uu____10042 in
                                FStar_Util.Inr uu____10041)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____10056 =
                             let uu____10057 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____10057.FStar_Syntax_Syntax.n in
                           (match uu____10056 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____10064 ->
                                let uu____10065 =
                                  let uu____10066 = is_cons head1 in
                                  Prims.op_Negation uu____10066 in
                                FStar_Util.Inr uu____10065))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____10100)::rest_a,(p1,uu____10103)::rest_p) ->
                      let uu____10131 = matches_pat t1 p1 in
                      (match uu____10131 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____10145 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____10216 = matches_pat scrutinee1 p1 in
                      (match uu____10216 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____10226  ->
                                 let uu____10227 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____10228 =
                                   let uu____10229 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____10229
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____10227 uu____10228);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____10238 =
                                        let uu____10239 =
                                          let uu____10249 =
                                            FStar_Util.mk_ref (Some ([], t1)) in
                                          ([], t1, uu____10249, false) in
                                        Clos uu____10239 in
                                      uu____10238 :: env2) env1 s in
                             let uu____10272 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____10272))) in
                let uu____10273 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____10273
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___140_10287  ->
                match uu___140_10287 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | uu____10290 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____10294 -> d in
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
            let uu___193_10314 = config s e in
            {
              steps = (uu___193_10314.steps);
              tcenv = (uu___193_10314.tcenv);
              delta_level = (uu___193_10314.delta_level);
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
      fun t  -> let uu____10333 = config s e in norm_comp uu____10333 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____10340 = config [] env in norm_universe uu____10340 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun c  ->
      let uu____10347 = config [] env in ghost_to_pure_aux uu____10347 [] c
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
        let uu____10359 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____10359 in
      let uu____10360 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____10360
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | Some pure_eff ->
            let uu___194_10362 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___194_10362.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___194_10362.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____10363  ->
                    let uu____10364 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____10364))
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
            ((let uu____10377 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10377);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____10386 = config [AllowUnboundUniverses] env in
          norm_comp uu____10386 [] c
        with
        | e ->
            ((let uu____10390 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10390);
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
                   let uu____10427 =
                     let uu____10428 =
                       let uu____10433 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____10433) in
                     FStar_Syntax_Syntax.Tm_refine uu____10428 in
                   mk uu____10427 t01.FStar_Syntax_Syntax.pos
               | uu____10438 -> t2)
          | uu____10439 -> t2 in
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
        let uu____10461 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____10461 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____10477 ->
                 let uu____10481 = FStar_Syntax_Util.abs_formals e in
                 (match uu____10481 with
                  | (actuals,uu____10492,uu____10493) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____10515 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____10515 with
                         | (binders,args) ->
                             let uu____10525 =
                               FStar_Syntax_Syntax.mk_Tm_app e args None
                                 e.FStar_Syntax_Syntax.pos in
                             let uu____10528 =
                               let uu____10535 =
                                 FStar_All.pipe_right
                                   (FStar_Syntax_Util.lcomp_of_comp c)
                                   (fun _0_44  -> FStar_Util.Inl _0_44) in
                               FStar_All.pipe_right uu____10535
                                 (fun _0_45  -> Some _0_45) in
                             FStar_Syntax_Util.abs binders uu____10525
                               uu____10528)))
let eta_expand:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____10571 =
        let uu____10575 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
        (uu____10575, (t.FStar_Syntax_Syntax.n)) in
      match uu____10571 with
      | (Some sort,uu____10582) ->
          let uu____10584 = mk sort t.FStar_Syntax_Syntax.pos in
          eta_expand_with_type env t uu____10584
      | (uu____10585,FStar_Syntax_Syntax.Tm_name x) ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____10589 ->
          let uu____10593 = FStar_Syntax_Util.head_and_args t in
          (match uu____10593 with
           | (head1,args) ->
               let uu____10619 =
                 let uu____10620 = FStar_Syntax_Subst.compress head1 in
                 uu____10620.FStar_Syntax_Syntax.n in
               (match uu____10619 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____10623,thead) ->
                    let uu____10637 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____10637 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____10668 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___199_10672 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___199_10672.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___199_10672.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___199_10672.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___199_10672.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___199_10672.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___199_10672.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ = None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___199_10672.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___199_10672.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___199_10672.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___199_10672.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___199_10672.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___199_10672.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___199_10672.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___199_10672.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___199_10672.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___199_10672.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___199_10672.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___199_10672.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___199_10672.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___199_10672.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___199_10672.FStar_TypeChecker_Env.qname_and_index)
                                 }) t in
                            match uu____10668 with
                            | (uu____10673,ty,uu____10675) ->
                                eta_expand_with_type env t ty))
                | uu____10676 ->
                    let uu____10677 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___200_10681 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___200_10681.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___200_10681.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___200_10681.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___200_10681.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___200_10681.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___200_10681.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ = None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___200_10681.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___200_10681.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___200_10681.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___200_10681.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___200_10681.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___200_10681.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___200_10681.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___200_10681.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___200_10681.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___200_10681.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___200_10681.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___200_10681.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___200_10681.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___200_10681.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___200_10681.FStar_TypeChecker_Env.qname_and_index)
                         }) t in
                    (match uu____10677 with
                     | (uu____10682,ty,uu____10684) ->
                         eta_expand_with_type env t ty)))