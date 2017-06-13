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
  fun projectee  -> match projectee with | Beta  -> true | uu____12 -> false
let uu___is_Iota: step -> Prims.bool =
  fun projectee  -> match projectee with | Iota  -> true | uu____16 -> false
let uu___is_Zeta: step -> Prims.bool =
  fun projectee  -> match projectee with | Zeta  -> true | uu____20 -> false
let uu___is_Exclude: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____25 -> false
let __proj__Exclude__item___0: step -> step =
  fun projectee  -> match projectee with | Exclude _0 -> _0
let uu___is_WHNF: step -> Prims.bool =
  fun projectee  -> match projectee with | WHNF  -> true | uu____36 -> false
let uu___is_Primops: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____40 -> false
let uu___is_Eager_unfolding: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____44 -> false
let uu___is_Inlining: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____48 -> false
let uu___is_NoDeltaSteps: step -> Prims.bool =
  fun projectee  ->
    match projectee with | NoDeltaSteps  -> true | uu____52 -> false
let uu___is_UnfoldUntil: step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____57 -> false
let __proj__UnfoldUntil__item___0: step -> FStar_Syntax_Syntax.delta_depth =
  fun projectee  -> match projectee with | UnfoldUntil _0 -> _0
let uu___is_PureSubtermsWithinComputations: step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____68 -> false
let uu___is_Simplify: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____72 -> false
let uu___is_EraseUniverses: step -> Prims.bool =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____76 -> false
let uu___is_AllowUnboundUniverses: step -> Prims.bool =
  fun projectee  ->
    match projectee with | AllowUnboundUniverses  -> true | uu____80 -> false
let uu___is_Reify: step -> Prims.bool =
  fun projectee  -> match projectee with | Reify  -> true | uu____84 -> false
let uu___is_CompressUvars: step -> Prims.bool =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____88 -> false
let uu___is_NoFullNorm: step -> Prims.bool =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____92 -> false
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
    match projectee with | Clos _0 -> true | uu____175 -> false
let __proj__Clos__item___0:
  closure ->
    (closure Prims.list* FStar_Syntax_Syntax.term* (closure Prims.list*
      FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo* Prims.bool)
  = fun projectee  -> match projectee with | Clos _0 -> _0
let uu___is_Univ: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____214 -> false
let __proj__Univ__item___0: closure -> FStar_Syntax_Syntax.universe =
  fun projectee  -> match projectee with | Univ _0 -> _0
let uu___is_Dummy: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____225 -> false
type env = closure Prims.list
let closure_to_string: closure -> Prims.string =
  fun uu___131_229  ->
    match uu___131_229 with
    | Clos (uu____230,t,uu____232,uu____233) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____244 -> "Univ"
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
    match projectee with | Arg _0 -> true | uu____371 -> false
let __proj__Arg__item___0:
  stack_elt -> (closure* FStar_Syntax_Syntax.aqual* FStar_Range.range) =
  fun projectee  -> match projectee with | Arg _0 -> _0
let uu___is_UnivArgs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____395 -> false
let __proj__UnivArgs__item___0:
  stack_elt -> (FStar_Syntax_Syntax.universe Prims.list* FStar_Range.range) =
  fun projectee  -> match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____419 -> false
let __proj__MemoLazy__item___0:
  stack_elt -> (env* FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo =
  fun projectee  -> match projectee with | MemoLazy _0 -> _0
let uu___is_Match: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____446 -> false
let __proj__Match__item___0: stack_elt -> (env* branches* FStar_Range.range)
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Abs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____475 -> false
let __proj__Abs__item___0:
  stack_elt ->
    (env* FStar_Syntax_Syntax.binders* env*
      (FStar_Syntax_Syntax.lcomp,FStar_Syntax_Syntax.residual_comp)
      FStar_Util.either option* FStar_Range.range)
  = fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____514 -> false
let __proj__App__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.aqual* FStar_Range.range)
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Meta: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____537 -> false
let __proj__Meta__item___0:
  stack_elt -> (FStar_Syntax_Syntax.metadata* FStar_Range.range) =
  fun projectee  -> match projectee with | Meta _0 -> _0
let uu___is_Let: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____559 -> false
let __proj__Let__item___0:
  stack_elt ->
    (env* FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.letbinding*
      FStar_Range.range)
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Steps: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Steps _0 -> true | uu____588 -> false
let __proj__Steps__item___0:
  stack_elt ->
    (steps* primitive_step Prims.list* FStar_TypeChecker_Env.delta_level
      Prims.list)
  = fun projectee  -> match projectee with | Steps _0 -> _0
let uu___is_Debug: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____615 -> false
let __proj__Debug__item___0: stack_elt -> FStar_Syntax_Syntax.term =
  fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list
let mk t r = FStar_Syntax_Syntax.mk t None r
let set_memo r t =
  let uu____663 = FStar_ST.read r in
  match uu____663 with
  | Some uu____668 -> failwith "Unexpected set_memo: thunk already evaluated"
  | None  -> FStar_ST.write r (Some t)
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____677 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____677 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___132_682  ->
    match uu___132_682 with
    | Arg (c,uu____684,uu____685) ->
        let uu____686 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____686
    | MemoLazy uu____687 -> "MemoLazy"
    | Abs (uu____691,bs,uu____693,uu____694,uu____695) ->
        let uu____702 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____702
    | UnivArgs uu____707 -> "UnivArgs"
    | Match uu____711 -> "Match"
    | App (t,uu____716,uu____717) ->
        let uu____718 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____718
    | Meta (m,uu____720) -> "Meta"
    | Let uu____721 -> "Let"
    | Steps (uu____726,uu____727,uu____728) -> "Steps"
    | Debug t ->
        let uu____734 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____734
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____740 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____740 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____754 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____754 then f () else ()
let is_empty uu___133_763 =
  match uu___133_763 with | [] -> true | uu____765 -> false
let lookup_bvar env x =
  try FStar_List.nth env x.FStar_Syntax_Syntax.index
  with
  | uu____783 ->
      let uu____784 =
        let uu____785 = FStar_Syntax_Print.db_to_string x in
        FStar_Util.format1 "Failed to find %s\n" uu____785 in
      failwith uu____784
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
          let uu____816 =
            FStar_List.fold_left
              (fun uu____825  ->
                 fun u1  ->
                   match uu____825 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____840 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____840 with
                        | (k_u,n1) ->
                            let uu____849 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____849
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____816 with
          | (uu____859,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____875 = FStar_List.nth env x in
                 match uu____875 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____878 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____882 ->
                   let uu____883 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____883
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____887 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____892 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____897 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____897 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____908 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____908 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____913 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____916 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____916 with
                                  | (uu____919,m) -> n1 <= m)) in
                        if uu____913 then rest1 else us1
                    | uu____923 -> us1)
               | uu____926 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____929 = aux u3 in
              FStar_List.map (fun _0_30  -> FStar_Syntax_Syntax.U_succ _0_30)
                uu____929 in
        let uu____931 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____931
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____933 = aux u in
           match uu____933 with
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
          (fun uu____1030  ->
             let uu____1031 = FStar_Syntax_Print.tag_of_term t in
             let uu____1032 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1031
               uu____1032);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1033 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1036 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____1057 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____1058 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____1059 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____1060 -> t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____1072 =
                    let uu____1073 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____1073 in
                  mk uu____1072 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t2,us) ->
                  let uu____1080 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t2 uu____1080
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____1082 = lookup_bvar env x in
                  (match uu____1082 with
                   | Univ uu____1083 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____1087) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____1155 = closures_as_binders_delayed cfg env bs in
                  (match uu____1155 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____1175 =
                         let uu____1176 =
                           let uu____1191 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____1191) in
                         FStar_Syntax_Syntax.Tm_abs uu____1176 in
                       mk uu____1175 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____1221 = closures_as_binders_delayed cfg env bs in
                  (match uu____1221 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____1252 =
                    let uu____1259 =
                      let uu____1263 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____1263] in
                    closures_as_binders_delayed cfg env uu____1259 in
                  (match uu____1252 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____1277 =
                         let uu____1278 =
                           let uu____1283 =
                             let uu____1284 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____1284
                               FStar_Pervasives.fst in
                           (uu____1283, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____1278 in
                       mk uu____1277 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____1352 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____1352
                    | FStar_Util.Inr c ->
                        let uu____1366 = close_comp cfg env c in
                        FStar_Util.Inr uu____1366 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____1381 =
                    let uu____1382 =
                      let uu____1400 = closure_as_term_delayed cfg env t11 in
                      (uu____1400, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____1382 in
                  mk uu____1381 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____1438 =
                    let uu____1439 =
                      let uu____1444 = closure_as_term_delayed cfg env t' in
                      let uu____1447 =
                        let uu____1448 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____1448 in
                      (uu____1444, uu____1447) in
                    FStar_Syntax_Syntax.Tm_meta uu____1439 in
                  mk uu____1438 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____1490 =
                    let uu____1491 =
                      let uu____1496 = closure_as_term_delayed cfg env t' in
                      let uu____1499 =
                        let uu____1500 =
                          let uu____1505 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____1505) in
                        FStar_Syntax_Syntax.Meta_monadic uu____1500 in
                      (uu____1496, uu____1499) in
                    FStar_Syntax_Syntax.Tm_meta uu____1491 in
                  mk uu____1490 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____1524 =
                    let uu____1525 =
                      let uu____1530 = closure_as_term_delayed cfg env t' in
                      let uu____1533 =
                        let uu____1534 =
                          let uu____1540 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____1540) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____1534 in
                      (uu____1530, uu____1533) in
                    FStar_Syntax_Syntax.Tm_meta uu____1525 in
                  mk uu____1524 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____1553 =
                    let uu____1554 =
                      let uu____1559 = closure_as_term_delayed cfg env t' in
                      (uu____1559, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____1554 in
                  mk uu____1553 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____1580  -> Dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let body1 =
                    match lb.FStar_Syntax_Syntax.lbname with
                    | FStar_Util.Inr uu____1591 -> body
                    | FStar_Util.Inl uu____1592 ->
                        closure_as_term cfg (Dummy :: env0) body in
                  let lb1 =
                    let uu___147_1594 = lb in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___147_1594.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___147_1594.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = typ;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___147_1594.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = def
                    } in
                  mk (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((uu____1601,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____1625  -> fun env2  -> Dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____1630 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____1630
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____1634  -> fun env2  -> Dummy :: env2) lbs
                          env_univs in
                    let uu___148_1637 = lb in
                    let uu____1638 =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let uu____1641 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___148_1637.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___148_1637.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = uu____1638;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___148_1637.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____1641
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____1652  -> fun env1  -> Dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____1707 =
                    match uu____1707 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____1753 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____1769 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____1803  ->
                                        fun uu____1804  ->
                                          match (uu____1803, uu____1804) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____1869 =
                                                norm_pat env3 p1 in
                                              (match uu____1869 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____1769 with
                               | (pats1,env3) ->
                                   ((let uu___149_1935 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.ty =
                                         (uu___149_1935.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___149_1935.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___150_1949 = x in
                                let uu____1950 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___150_1949.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___150_1949.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1950
                                } in
                              ((let uu___151_1956 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___151_1956.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___151_1956.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___152_1961 = x in
                                let uu____1962 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___152_1961.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___152_1961.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1962
                                } in
                              ((let uu___153_1968 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___153_1968.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___153_1968.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___154_1978 = x in
                                let uu____1979 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___154_1978.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___154_1978.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1979
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___155_1986 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___155_1986.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___155_1986.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____1989 = norm_pat env1 pat in
                        (match uu____1989 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | None  -> None
                               | Some w ->
                                   let uu____2013 =
                                     closure_as_term cfg env2 w in
                                   Some uu____2013 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____2018 =
                    let uu____2019 =
                      let uu____2035 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____2035) in
                    FStar_Syntax_Syntax.Tm_match uu____2019 in
                  mk uu____2018 t1.FStar_Syntax_Syntax.pos))
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
        | uu____2088 -> closure_as_term cfg env t
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
        | uu____2104 ->
            FStar_List.map
              (fun uu____2114  ->
                 match uu____2114 with
                 | (x,imp) ->
                     let uu____2129 = closure_as_term_delayed cfg env x in
                     (uu____2129, imp)) args
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
        let uu____2141 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____2165  ->
                  fun uu____2166  ->
                    match (uu____2165, uu____2166) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___156_2210 = b in
                          let uu____2211 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___156_2210.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___156_2210.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____2211
                          } in
                        let env2 = Dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____2141 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____2258 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____2270 = closure_as_term_delayed cfg env t in
                 let uu____2271 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____2270 uu____2271
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____2281 = closure_as_term_delayed cfg env t in
                 let uu____2282 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____2281 uu____2282
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
                        (fun uu___134_2298  ->
                           match uu___134_2298 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____2302 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____2302
                           | f -> f)) in
                 let uu____2306 =
                   let uu___157_2307 = c1 in
                   let uu____2308 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____2308;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___157_2307.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____2306)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.cflags Prims.list =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_List.filter
         (fun uu___135_2312  ->
            match uu___135_2312 with
            | FStar_Syntax_Syntax.DECREASES uu____2313 -> false
            | uu____2316 -> true))
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
            let uu____2344 = FStar_Syntax_Util.is_total_lcomp lc in
            if uu____2344
            then
              Some
                (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, flags))
            else
              (let uu____2361 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
               if uu____2361
               then
                 Some
                   (FStar_Util.Inr
                      (FStar_Syntax_Const.effect_GTot_lid, flags))
               else
                 Some
                   (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags)))
        | uu____2387 -> lopt
let built_in_primitive_steps: primitive_step Prims.list =
  let const_as_tm c p = mk (FStar_Syntax_Syntax.Tm_constant c) p in
  let int_as_const p i =
    let uu____2411 =
      let uu____2412 =
        let uu____2418 = FStar_Util.string_of_int i in (uu____2418, None) in
      FStar_Const.Const_int uu____2412 in
    const_as_tm uu____2411 p in
  let bool_as_const p b = const_as_tm (FStar_Const.Const_bool b) p in
  let string_as_const p b =
    const_as_tm
      (FStar_Const.Const_string ((FStar_Util.bytes_of_string b), p)) p in
  let arg_as_int uu____2445 =
    match uu____2445 with
    | (a,uu____2450) ->
        let uu____2452 =
          let uu____2453 = FStar_Syntax_Subst.compress a in
          uu____2453.FStar_Syntax_Syntax.n in
        (match uu____2452 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i,None ))
             ->
             let uu____2463 = FStar_Util.int_of_string i in Some uu____2463
         | uu____2464 -> None) in
  let arg_as_bounded_int uu____2473 =
    match uu____2473 with
    | (a,uu____2480) ->
        let uu____2484 =
          let uu____2485 = FStar_Syntax_Subst.compress a in
          uu____2485.FStar_Syntax_Syntax.n in
        (match uu____2484 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.tk = uu____2492;
                FStar_Syntax_Syntax.pos = uu____2493;
                FStar_Syntax_Syntax.vars = uu____2494;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,None ));
                                                            FStar_Syntax_Syntax.tk
                                                              = uu____2496;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____2497;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____2498;_},uu____2499)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____2530 =
               let uu____2533 = FStar_Util.int_of_string i in
               (fv1, uu____2533) in
             Some uu____2530
         | uu____2536 -> None) in
  let arg_as_bool uu____2545 =
    match uu____2545 with
    | (a,uu____2550) ->
        let uu____2552 =
          let uu____2553 = FStar_Syntax_Subst.compress a in
          uu____2553.FStar_Syntax_Syntax.n in
        (match uu____2552 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
             Some b
         | uu____2558 -> None) in
  let arg_as_char uu____2565 =
    match uu____2565 with
    | (a,uu____2570) ->
        let uu____2572 =
          let uu____2573 = FStar_Syntax_Subst.compress a in
          uu____2573.FStar_Syntax_Syntax.n in
        (match uu____2572 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
             Some c
         | uu____2578 -> None) in
  let arg_as_string uu____2585 =
    match uu____2585 with
    | (a,uu____2590) ->
        let uu____2592 =
          let uu____2593 = FStar_Syntax_Subst.compress a in
          uu____2593.FStar_Syntax_Syntax.n in
        (match uu____2592 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (bytes,uu____2598)) -> Some (FStar_Util.string_of_bytes bytes)
         | uu____2601 -> None) in
  let arg_as_list f uu____2622 =
    match uu____2622 with
    | (a,uu____2631) ->
        let rec sequence l =
          match l with
          | [] -> Some []
          | (None )::uu____2650 -> None
          | (Some x)::xs ->
              let uu____2660 = sequence xs in
              (match uu____2660 with
               | None  -> None
               | Some xs' -> Some (x :: xs')) in
        let uu____2671 = FStar_Syntax_Util.list_elements a in
        (match uu____2671 with
         | None  -> None
         | Some elts ->
             let uu____2681 =
               FStar_List.map
                 (fun x  ->
                    let uu____2686 = FStar_Syntax_Syntax.as_arg x in
                    f uu____2686) elts in
             sequence uu____2681) in
  let lift_unary f aopts =
    match aopts with
    | (Some a)::[] -> let uu____2716 = f a in Some uu____2716
    | uu____2717 -> None in
  let lift_binary f aopts =
    match aopts with
    | (Some a0)::(Some a1)::[] -> let uu____2756 = f a0 a1 in Some uu____2756
    | uu____2757 -> None in
  let unary_op as_a f r args =
    let uu____2801 = FStar_List.map as_a args in lift_unary (f r) uu____2801 in
  let binary_op as_a f r args =
    let uu____2851 = FStar_List.map as_a args in lift_binary (f r) uu____2851 in
  let as_primitive_step uu____2868 =
    match uu____2868 with
    | (l,arity,f) ->
        { name = l; arity; strong_reduction_ok = true; interpretation = f } in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  -> fun x  -> let uu____2906 = f x in int_as_const r uu____2906) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2929 = f x y in int_as_const r uu____2929) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  -> fun x  -> let uu____2946 = f x in bool_as_const r uu____2946) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2969 = f x y in bool_as_const r uu____2969) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2992 = f x y in string_as_const r uu____2992) in
  let list_of_string' rng s =
    let name l =
      let uu____3006 =
        let uu____3007 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            None in
        FStar_Syntax_Syntax.Tm_fvar uu____3007 in
      mk uu____3006 rng in
    let char_t = name FStar_Syntax_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____3017 =
      let uu____3019 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____3019 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____3017 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Const.exp_string s in
  let string_of_int1 rng i =
    let uu____3041 = FStar_Util.string_of_int i in
    string_as_const rng uu____3041 in
  let string_of_bool1 rng b =
    string_as_const rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____3057 = FStar_Util.string_of_int i in
    string_as_const rng uu____3057 in
  let string_of_bool2 rng b =
    string_as_const rng (if b then "true" else "false") in
  let basic_ops =
    let uu____3076 =
      let uu____3086 =
        let uu____3096 =
          let uu____3106 =
            let uu____3116 =
              let uu____3126 =
                let uu____3136 =
                  let uu____3146 =
                    let uu____3156 =
                      let uu____3166 =
                        let uu____3176 =
                          let uu____3186 =
                            let uu____3196 =
                              let uu____3206 =
                                let uu____3216 =
                                  let uu____3226 =
                                    let uu____3236 =
                                      let uu____3245 =
                                        FStar_Syntax_Const.p2l
                                          ["FStar";
                                          "String";
                                          "list_of_string"] in
                                      (uu____3245, (Prims.parse_int "1"),
                                        (unary_op arg_as_string
                                           list_of_string')) in
                                    let uu____3251 =
                                      let uu____3261 =
                                        let uu____3270 =
                                          FStar_Syntax_Const.p2l
                                            ["FStar";
                                            "String";
                                            "string_of_list"] in
                                        (uu____3270, (Prims.parse_int "1"),
                                          (unary_op (arg_as_list arg_as_char)
                                             string_of_list')) in
                                      [uu____3261] in
                                    uu____3236 :: uu____3251 in
                                  (FStar_Syntax_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_bool string_of_bool2))
                                    :: uu____3226 in
                                (FStar_Syntax_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (unary_op arg_as_int string_of_int2)) ::
                                  uu____3216 in
                              (FStar_Syntax_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____3206 in
                            (FStar_Syntax_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____3196 in
                          (FStar_Syntax_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____3186 in
                        (FStar_Syntax_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____3176 in
                      (FStar_Syntax_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____3166 in
                    (FStar_Syntax_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
                      :: uu____3156 in
                  (FStar_Syntax_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____3146 in
                (FStar_Syntax_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____3136 in
              (FStar_Syntax_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____3126 in
            (FStar_Syntax_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____3116 in
          (FStar_Syntax_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____3106 in
        (FStar_Syntax_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____3096 in
      (FStar_Syntax_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____3086 in
    (FStar_Syntax_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____3076 in
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
      let uu____3565 =
        let uu____3566 =
          let uu____3567 = FStar_Syntax_Syntax.as_arg c in [uu____3567] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____3566 in
      uu____3565 None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____3591 =
              let uu____3600 = FStar_Syntax_Const.p2l ["FStar"; m; "add"] in
              (uu____3600, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____3609  ->
                        fun uu____3610  ->
                          match (uu____3609, uu____3610) with
                          | ((int_to_t1,x),(uu____3621,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____3627 =
              let uu____3637 =
                let uu____3646 = FStar_Syntax_Const.p2l ["FStar"; m; "sub"] in
                (uu____3646, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____3655  ->
                          fun uu____3656  ->
                            match (uu____3655, uu____3656) with
                            | ((int_to_t1,x),(uu____3667,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____3673 =
                let uu____3683 =
                  let uu____3692 = FStar_Syntax_Const.p2l ["FStar"; m; "mul"] in
                  (uu____3692, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____3701  ->
                            fun uu____3702  ->
                              match (uu____3701, uu____3702) with
                              | ((int_to_t1,x),(uu____3713,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____3683] in
              uu____3637 :: uu____3673 in
            uu____3591 :: uu____3627)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_bool rng args =
    match args with
    | (_typ,uu____3779)::(a1,uu____3781)::(a2,uu____3783)::[] ->
        let uu____3812 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3812 with
         | FStar_Syntax_Util.Equal  ->
             let uu____3814 =
               mk
                 (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_bool true)) rng in
             Some uu____3814
         | FStar_Syntax_Util.NotEqual  ->
             let uu____3819 =
               mk
                 (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_bool false)) rng in
             Some uu____3819
         | uu____3824 -> None)
    | uu____3825 -> failwith "Unexpected number of arguments" in
  let interp_prop r args =
    match args with
    | (_typ,uu____3838)::(a1,uu____3840)::(a2,uu____3842)::[] ->
        let uu____3871 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3871 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___158_3875 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___158_3875.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___158_3875.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___158_3875.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___159_3882 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___159_3882.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___159_3882.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___159_3882.FStar_Syntax_Syntax.vars)
                })
         | uu____3887 -> None)
    | (_typ,uu____3889)::uu____3890::(a1,uu____3892)::(a2,uu____3894)::[] ->
        let uu____3931 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3931 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___158_3935 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___158_3935.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___158_3935.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___158_3935.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___159_3942 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___159_3942.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___159_3942.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___159_3942.FStar_Syntax_Syntax.vars)
                })
         | uu____3947 -> None)
    | uu____3948 -> failwith "Unexpected number of arguments" in
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
      let uu____3959 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops cfg.steps) in
      if uu____3959
      then tm
      else
        (let uu____3961 = FStar_Syntax_Util.head_and_args tm in
         match uu____3961 with
         | (head1,args) ->
             let uu____3987 =
               let uu____3988 = FStar_Syntax_Util.un_uinst head1 in
               uu____3988.FStar_Syntax_Syntax.n in
             (match uu____3987 with
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____3992 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps in
                  (match uu____3992 with
                   | None  -> tm
                   | Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then tm
                       else
                         (let uu____4004 =
                            prim_step.interpretation
                              head1.FStar_Syntax_Syntax.pos args in
                          match uu____4004 with
                          | None  -> tm
                          | Some reduced -> reduced))
              | uu____4007 -> tm))
let reduce_equality:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___160_4014 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___160_4014.tcenv);
           delta_level = (uu___160_4014.delta_level);
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
        let uu___161_4036 = t in
        {
          FStar_Syntax_Syntax.n = (uu___161_4036.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___161_4036.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___161_4036.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid ->
            Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid ->
            Some false
        | uu____4055 -> None in
      let simplify arg = ((simp_t (fst arg)), arg) in
      let uu____4082 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps) in
      if uu____4082
      then reduce_primops cfg tm
      else
        (match tm.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.tk = uu____4085;
                     FStar_Syntax_Syntax.pos = uu____4086;
                     FStar_Syntax_Syntax.vars = uu____4087;_},uu____4088);
                FStar_Syntax_Syntax.tk = uu____4089;
                FStar_Syntax_Syntax.pos = uu____4090;
                FStar_Syntax_Syntax.vars = uu____4091;_},args)
             ->
             let uu____4111 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____4111
             then
               let uu____4112 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____4112 with
                | (Some (true ),uu____4145)::(uu____4146,(arg,uu____4148))::[]
                    -> arg
                | (uu____4189,(arg,uu____4191))::(Some (true ),uu____4192)::[]
                    -> arg
                | (Some (false ),uu____4233)::uu____4234::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4272::(Some (false ),uu____4273)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4311 -> tm)
             else
               (let uu____4321 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____4321
                then
                  let uu____4322 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____4322 with
                  | (Some (true ),uu____4355)::uu____4356::[] ->
                      w FStar_Syntax_Util.t_true
                  | uu____4394::(Some (true ),uu____4395)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),uu____4433)::(uu____4434,(arg,uu____4436))::[]
                      -> arg
                  | (uu____4477,(arg,uu____4479))::(Some (false ),uu____4480)::[]
                      -> arg
                  | uu____4521 -> tm
                else
                  (let uu____4531 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____4531
                   then
                     let uu____4532 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____4532 with
                     | uu____4565::(Some (true ),uu____4566)::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (false ),uu____4604)::uu____4605::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____4643)::(uu____4644,(arg,uu____4646))::[]
                         -> arg
                     | uu____4687 -> tm
                   else
                     (let uu____4697 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____4697
                      then
                        let uu____4698 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____4698 with
                        | (Some (true ),uu____4731)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____4755)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____4779 -> tm
                      else
                        (let uu____4789 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid in
                         if uu____4789
                         then
                           match args with
                           | (t,uu____4791)::[] ->
                               let uu____4804 =
                                 let uu____4805 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____4805.FStar_Syntax_Syntax.n in
                               (match uu____4804 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____4808::[],body,uu____4810) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____4836 -> tm)
                                | uu____4838 -> tm)
                           | (uu____4839,Some (FStar_Syntax_Syntax.Implicit
                              uu____4840))::(t,uu____4842)::[] ->
                               let uu____4869 =
                                 let uu____4870 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____4870.FStar_Syntax_Syntax.n in
                               (match uu____4869 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____4873::[],body,uu____4875) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____4901 -> tm)
                                | uu____4903 -> tm)
                           | uu____4904 -> tm
                         else
                           (let uu____4911 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid in
                            if uu____4911
                            then
                              match args with
                              | (t,uu____4913)::[] ->
                                  let uu____4926 =
                                    let uu____4927 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____4927.FStar_Syntax_Syntax.n in
                                  (match uu____4926 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____4930::[],body,uu____4932) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____4958 -> tm)
                                   | uu____4960 -> tm)
                              | (uu____4961,Some
                                 (FStar_Syntax_Syntax.Implicit uu____4962))::
                                  (t,uu____4964)::[] ->
                                  let uu____4991 =
                                    let uu____4992 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____4992.FStar_Syntax_Syntax.n in
                                  (match uu____4991 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____4995::[],body,uu____4997) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5023 -> tm)
                                   | uu____5025 -> tm)
                              | uu____5026 -> tm
                            else reduce_equality cfg tm)))))
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                FStar_Syntax_Syntax.tk = uu____5034;
                FStar_Syntax_Syntax.pos = uu____5035;
                FStar_Syntax_Syntax.vars = uu____5036;_},args)
             ->
             let uu____5052 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____5052
             then
               let uu____5053 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____5053 with
                | (Some (true ),uu____5086)::(uu____5087,(arg,uu____5089))::[]
                    -> arg
                | (uu____5130,(arg,uu____5132))::(Some (true ),uu____5133)::[]
                    -> arg
                | (Some (false ),uu____5174)::uu____5175::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____5213::(Some (false ),uu____5214)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____5252 -> tm)
             else
               (let uu____5262 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____5262
                then
                  let uu____5263 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____5263 with
                  | (Some (true ),uu____5296)::uu____5297::[] ->
                      w FStar_Syntax_Util.t_true
                  | uu____5335::(Some (true ),uu____5336)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),uu____5374)::(uu____5375,(arg,uu____5377))::[]
                      -> arg
                  | (uu____5418,(arg,uu____5420))::(Some (false ),uu____5421)::[]
                      -> arg
                  | uu____5462 -> tm
                else
                  (let uu____5472 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____5472
                   then
                     let uu____5473 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____5473 with
                     | uu____5506::(Some (true ),uu____5507)::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (false ),uu____5545)::uu____5546::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____5584)::(uu____5585,(arg,uu____5587))::[]
                         -> arg
                     | uu____5628 -> tm
                   else
                     (let uu____5638 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____5638
                      then
                        let uu____5639 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____5639 with
                        | (Some (true ),uu____5672)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____5696)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____5720 -> tm
                      else
                        (let uu____5730 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid in
                         if uu____5730
                         then
                           match args with
                           | (t,uu____5732)::[] ->
                               let uu____5745 =
                                 let uu____5746 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5746.FStar_Syntax_Syntax.n in
                               (match uu____5745 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5749::[],body,uu____5751) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5777 -> tm)
                                | uu____5779 -> tm)
                           | (uu____5780,Some (FStar_Syntax_Syntax.Implicit
                              uu____5781))::(t,uu____5783)::[] ->
                               let uu____5810 =
                                 let uu____5811 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5811.FStar_Syntax_Syntax.n in
                               (match uu____5810 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5814::[],body,uu____5816) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5842 -> tm)
                                | uu____5844 -> tm)
                           | uu____5845 -> tm
                         else
                           (let uu____5852 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid in
                            if uu____5852
                            then
                              match args with
                              | (t,uu____5854)::[] ->
                                  let uu____5867 =
                                    let uu____5868 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5868.FStar_Syntax_Syntax.n in
                                  (match uu____5867 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5871::[],body,uu____5873) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5899 -> tm)
                                   | uu____5901 -> tm)
                              | (uu____5902,Some
                                 (FStar_Syntax_Syntax.Implicit uu____5903))::
                                  (t,uu____5905)::[] ->
                                  let uu____5932 =
                                    let uu____5933 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5933.FStar_Syntax_Syntax.n in
                                  (match uu____5932 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5936::[],body,uu____5938) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5964 -> tm)
                                   | uu____5966 -> tm)
                              | uu____5967 -> tm
                            else reduce_equality cfg tm)))))
         | uu____5974 -> tm)
let is_norm_request hd1 args =
  let uu____5989 =
    let uu____5993 =
      let uu____5994 = FStar_Syntax_Util.un_uinst hd1 in
      uu____5994.FStar_Syntax_Syntax.n in
    (uu____5993, args) in
  match uu____5989 with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5999::uu____6000::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize_term
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6003::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize
  | uu____6005 -> false
let get_norm_request args =
  match args with
  | uu____6024::(tm,uu____6026)::[] -> tm
  | (tm,uu____6036)::[] -> tm
  | uu____6041 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___136_6048  ->
    match uu___136_6048 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.tk = uu____6050;
           FStar_Syntax_Syntax.pos = uu____6051;
           FStar_Syntax_Syntax.vars = uu____6052;_},uu____6053,uu____6054))::uu____6055
        -> true
    | uu____6061 -> false
let is_fstar_tactics_embed: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____6066 =
      let uu____6067 = FStar_Syntax_Util.un_uinst t in
      uu____6067.FStar_Syntax_Syntax.n in
    match uu____6066 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Syntax_Const.fstar_tactics_embed_lid
    | uu____6071 -> false
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
            (fun uu____6185  ->
               let uu____6186 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____6187 = FStar_Syntax_Print.term_to_string t1 in
               let uu____6188 =
                 let uu____6189 =
                   let uu____6191 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives.fst uu____6191 in
                 stack_to_string uu____6189 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____6186
                 uu____6187 uu____6188);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____6203 ->
               failwith "Impossible"
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____6224 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____6235 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____6236 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6237;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____6238;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6243;
                 FStar_Syntax_Syntax.fv_delta = uu____6244;
                 FStar_Syntax_Syntax.fv_qual = Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6248;
                 FStar_Syntax_Syntax.fv_delta = uu____6249;
                 FStar_Syntax_Syntax.fv_qual = Some
                   (FStar_Syntax_Syntax.Record_ctor uu____6250);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.tk = uu____6258;
                  FStar_Syntax_Syntax.pos = uu____6259;
                  FStar_Syntax_Syntax.vars = uu____6260;_},uu____6261)
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Syntax_Const.fstar_tactics_embed_lid
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               is_fstar_tactics_embed hd1 ->
               let args1 = closures_as_args_delayed cfg env args in
               let t2 =
                 let uu___162_6301 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd1, args1));
                   FStar_Syntax_Syntax.tk =
                     (uu___162_6301.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___162_6301.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___162_6301.FStar_Syntax_Syntax.vars)
                 } in
               let t3 = reduce_primops cfg t2 in rebuild cfg env stack1 t3
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____6330 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____6330) && (is_norm_request hd1 args))
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
                 let uu___163_6343 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___163_6343.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___163_6343.primitive_steps)
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
                  FStar_Syntax_Syntax.tk = uu____6348;
                  FStar_Syntax_Syntax.pos = uu____6349;
                  FStar_Syntax_Syntax.vars = uu____6350;_},a1::a2::rest)
               ->
               let uu____6384 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6384 with
                | (hd1,uu____6395) ->
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
                    (FStar_Const.Const_reflect uu____6450);
                  FStar_Syntax_Syntax.tk = uu____6451;
                  FStar_Syntax_Syntax.pos = uu____6452;
                  FStar_Syntax_Syntax.vars = uu____6453;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____6476 = FStar_List.tl stack1 in
               norm cfg env uu____6476 (fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.tk = uu____6479;
                  FStar_Syntax_Syntax.pos = uu____6480;
                  FStar_Syntax_Syntax.vars = uu____6481;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____6504 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6504 with
                | (reify_head,uu____6515) ->
                    let a1 =
                      let uu____6531 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (fst a) in
                      FStar_Syntax_Subst.compress uu____6531 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____6534);
                            FStar_Syntax_Syntax.tk = uu____6535;
                            FStar_Syntax_Syntax.pos = uu____6536;
                            FStar_Syntax_Syntax.vars = uu____6537;_},a2::[])
                         -> norm cfg env stack1 (fst a2)
                     | uu____6562 ->
                         let stack2 =
                           (App
                              (reify_head, None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____6570 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____6570
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____6577 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____6577
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____6580 =
                      let uu____6584 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____6584, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____6580 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___137_6593  ->
                         match uu___137_6593 with
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
                    let uu____6597 = FStar_Syntax_Syntax.range_of_fv f in
                    FStar_TypeChecker_Env.set_range cfg.tcenv uu____6597 in
                  let uu____6598 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  match uu____6598 with
                  | None  ->
                      (log cfg
                         (fun uu____6609  ->
                            FStar_Util.print "Tm_fvar case 2\n" []);
                       rebuild cfg env stack1 t1)
                  | Some (us,t2) ->
                      (log cfg
                         (fun uu____6615  ->
                            let uu____6616 =
                              FStar_Syntax_Print.term_to_string t0 in
                            let uu____6617 =
                              FStar_Syntax_Print.term_to_string t2 in
                            FStar_Util.print2 ">>> Unfolded %s to %s\n"
                              uu____6616 uu____6617);
                       (let t3 =
                          let uu____6619 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 (UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant)) in
                          if uu____6619
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
                          | (UnivArgs (us',uu____6631))::stack2 ->
                              let env1 =
                                FStar_All.pipe_right us'
                                  (FStar_List.fold_left
                                     (fun env1  -> fun u  -> (Univ u) :: env1)
                                     env) in
                              norm cfg env1 stack2 t3
                          | uu____6644 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack1 t3
                          | uu____6645 ->
                              let uu____6646 =
                                let uu____6647 =
                                  FStar_Syntax_Print.lid_to_string
                                    (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                FStar_Util.format1
                                  "Impossible: missing universe instantiation on %s"
                                  uu____6647 in
                              failwith uu____6646
                        else norm cfg env stack1 t3)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____6654 = lookup_bvar env x in
               (match uu____6654 with
                | Univ uu____6655 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____6670 = FStar_ST.read r in
                      (match uu____6670 with
                       | Some (env2,t') ->
                           (log cfg
                              (fun uu____6689  ->
                                 let uu____6690 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____6691 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____6690
                                   uu____6691);
                            (let uu____6692 =
                               let uu____6693 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____6693.FStar_Syntax_Syntax.n in
                             match uu____6692 with
                             | FStar_Syntax_Syntax.Tm_abs uu____6696 ->
                                 norm cfg env2 stack1 t'
                             | uu____6711 -> rebuild cfg env2 stack1 t'))
                       | None  -> norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____6744)::uu____6745 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____6750)::uu____6751 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____6757,uu____6758))::stack_rest ->
                    (match c with
                     | Univ uu____6761 -> norm cfg (c :: env) stack_rest t1
                     | uu____6762 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____6765::[] ->
                              (match lopt with
                               | None  when FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____6778  ->
                                         let uu____6779 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6779);
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
                                           (fun uu___138_6793  ->
                                              match uu___138_6793 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____6794 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____6796  ->
                                         let uu____6797 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6797);
                                    norm cfg (c :: env) stack_rest body)
                               | Some (FStar_Util.Inl lc) when
                                   FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                                   ->
                                   (log cfg
                                      (fun uu____6808  ->
                                         let uu____6809 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6809);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____6810 when
                                   FStar_All.pipe_right cfg.steps
                                     (FStar_List.contains Reify)
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____6817 ->
                                   let cfg1 =
                                     let uu___164_6825 = cfg in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___164_6825.tcenv);
                                       delta_level =
                                         (uu___164_6825.delta_level);
                                       primitive_steps =
                                         (uu___164_6825.primitive_steps)
                                     } in
                                   let uu____6826 =
                                     closure_as_term cfg1 env t1 in
                                   rebuild cfg1 env stack1 uu____6826)
                          | uu____6827::tl1 ->
                              (log cfg
                                 (fun uu____6837  ->
                                    let uu____6838 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____6838);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___165_6862 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___165_6862.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____6875  ->
                          let uu____6876 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____6876);
                     norm cfg env stack2 t1)
                | (Debug uu____6877)::uu____6878 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____6880 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____6880
                    else
                      (let uu____6882 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____6882 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____6911 =
                                   let uu____6917 =
                                     let uu____6918 =
                                       let uu____6919 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____6919 in
                                     FStar_All.pipe_right uu____6918
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____6917
                                     (fun _0_31  -> FStar_Util.Inl _0_31) in
                                 FStar_All.pipe_right uu____6911
                                   (fun _0_32  -> Some _0_32)
                             | uu____6944 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____6958  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____6963  ->
                                 let uu____6964 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____6964);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___166_6974 = cfg in
                               let uu____6975 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___166_6974.steps);
                                 tcenv = (uu___166_6974.tcenv);
                                 delta_level = (uu___166_6974.delta_level);
                                 primitive_steps = uu____6975
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____6985)::uu____6986 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____6990 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____6990
                    else
                      (let uu____6992 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____6992 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7021 =
                                   let uu____7027 =
                                     let uu____7028 =
                                       let uu____7029 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7029 in
                                     FStar_All.pipe_right uu____7028
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7027
                                     (fun _0_33  -> FStar_Util.Inl _0_33) in
                                 FStar_All.pipe_right uu____7021
                                   (fun _0_34  -> Some _0_34)
                             | uu____7054 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7068  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7073  ->
                                 let uu____7074 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7074);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___166_7084 = cfg in
                               let uu____7085 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___166_7084.steps);
                                 tcenv = (uu___166_7084.tcenv);
                                 delta_level = (uu___166_7084.delta_level);
                                 primitive_steps = uu____7085
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____7095)::uu____7096 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7102 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7102
                    else
                      (let uu____7104 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7104 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7133 =
                                   let uu____7139 =
                                     let uu____7140 =
                                       let uu____7141 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7141 in
                                     FStar_All.pipe_right uu____7140
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7139
                                     (fun _0_35  -> FStar_Util.Inl _0_35) in
                                 FStar_All.pipe_right uu____7133
                                   (fun _0_36  -> Some _0_36)
                             | uu____7166 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7180  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7185  ->
                                 let uu____7186 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7186);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___166_7196 = cfg in
                               let uu____7197 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___166_7196.steps);
                                 tcenv = (uu___166_7196.tcenv);
                                 delta_level = (uu___166_7196.delta_level);
                                 primitive_steps = uu____7197
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____7207)::uu____7208 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7213 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7213
                    else
                      (let uu____7215 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7215 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7244 =
                                   let uu____7250 =
                                     let uu____7251 =
                                       let uu____7252 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7252 in
                                     FStar_All.pipe_right uu____7251
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7250
                                     (fun _0_37  -> FStar_Util.Inl _0_37) in
                                 FStar_All.pipe_right uu____7244
                                   (fun _0_38  -> Some _0_38)
                             | uu____7277 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7291  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7296  ->
                                 let uu____7297 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7297);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___166_7307 = cfg in
                               let uu____7308 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___166_7307.steps);
                                 tcenv = (uu___166_7307.tcenv);
                                 delta_level = (uu___166_7307.delta_level);
                                 primitive_steps = uu____7308
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____7318)::uu____7319 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7329 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7329
                    else
                      (let uu____7331 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7331 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7360 =
                                   let uu____7366 =
                                     let uu____7367 =
                                       let uu____7368 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7368 in
                                     FStar_All.pipe_right uu____7367
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7366
                                     (fun _0_39  -> FStar_Util.Inl _0_39) in
                                 FStar_All.pipe_right uu____7360
                                   (fun _0_40  -> Some _0_40)
                             | uu____7393 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7407  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7412  ->
                                 let uu____7413 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7413);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___166_7423 = cfg in
                               let uu____7424 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___166_7423.steps);
                                 tcenv = (uu___166_7423.tcenv);
                                 delta_level = (uu___166_7423.delta_level);
                                 primitive_steps = uu____7424
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7434 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7434
                    else
                      (let uu____7436 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7436 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7465 =
                                   let uu____7471 =
                                     let uu____7472 =
                                       let uu____7473 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7473 in
                                     FStar_All.pipe_right uu____7472
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7471
                                     (fun _0_41  -> FStar_Util.Inl _0_41) in
                                 FStar_All.pipe_right uu____7465
                                   (fun _0_42  -> Some _0_42)
                             | uu____7498 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7512  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7517  ->
                                 let uu____7518 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7518);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___166_7528 = cfg in
                               let uu____7529 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___166_7528.steps);
                                 tcenv = (uu___166_7528.tcenv);
                                 delta_level = (uu___166_7528.delta_level);
                                 primitive_steps = uu____7529
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
                      (fun uu____7561  ->
                         fun stack2  ->
                           match uu____7561 with
                           | (a,aq) ->
                               let uu____7569 =
                                 let uu____7570 =
                                   let uu____7574 =
                                     let uu____7575 =
                                       let uu____7585 =
                                         FStar_Util.mk_ref None in
                                       (env, a, uu____7585, false) in
                                     Clos uu____7575 in
                                   (uu____7574, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____7570 in
                               uu____7569 :: stack2) args) in
               (log cfg
                  (fun uu____7607  ->
                     let uu____7608 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____7608);
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
                             ((let uu___167_7629 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___167_7629.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___167_7629.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____7630 ->
                      let uu____7633 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7633)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____7636 = FStar_Syntax_Subst.open_term [(x, None)] f in
                  match uu____7636 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____7652 =
                          let uu____7653 =
                            let uu____7658 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___168_7659 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___168_7659.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___168_7659.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____7658) in
                          FStar_Syntax_Syntax.Tm_refine uu____7653 in
                        mk uu____7652 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____7672 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____7672
               else
                 (let uu____7674 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____7674 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____7680 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  -> fun uu____7686  -> Dummy :: env1)
                               env) in
                        norm_comp cfg uu____7680 c1 in
                      let t2 =
                        let uu____7693 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____7693 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____7736)::uu____7737 -> norm cfg env stack1 t11
                | (Arg uu____7742)::uu____7743 -> norm cfg env stack1 t11
                | (App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.tk = uu____7748;
                       FStar_Syntax_Syntax.pos = uu____7749;
                       FStar_Syntax_Syntax.vars = uu____7750;_},uu____7751,uu____7752))::uu____7753
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____7759)::uu____7760 ->
                    norm cfg env stack1 t11
                | uu____7765 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____7768  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____7781 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____7781
                        | FStar_Util.Inr c ->
                            let uu____7789 = norm_comp cfg env c in
                            FStar_Util.Inr uu____7789 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____7794 =
                        mk
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (t12, (tc1, tacopt1), l))
                          t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____7794)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____7845,{
                              FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                uu____7846;
                              FStar_Syntax_Syntax.lbunivs = uu____7847;
                              FStar_Syntax_Syntax.lbtyp = uu____7848;
                              FStar_Syntax_Syntax.lbeff = uu____7849;
                              FStar_Syntax_Syntax.lbdef = uu____7850;_}::uu____7851),uu____7852)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____7878 =
                 (let uu____7879 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____7879) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____7880 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____7880))) in
               if uu____7878
               then
                 let env1 =
                   let uu____7883 =
                     let uu____7884 =
                       let uu____7894 = FStar_Util.mk_ref None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____7894,
                         false) in
                     Clos uu____7884 in
                   uu____7883 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____7918 =
                    let uu____7921 =
                      let uu____7922 =
                        let uu____7923 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____7923
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____7922] in
                    FStar_Syntax_Subst.open_term uu____7921 body in
                  match uu____7918 with
                  | (bs,body1) ->
                      let lb1 =
                        let uu___169_7929 = lb in
                        let uu____7930 =
                          let uu____7933 =
                            let uu____7934 = FStar_List.hd bs in
                            FStar_All.pipe_right uu____7934
                              FStar_Pervasives.fst in
                          FStar_All.pipe_right uu____7933
                            (fun _0_43  -> FStar_Util.Inl _0_43) in
                        let uu____7943 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____7946 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = uu____7930;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___169_7929.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____7943;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___169_7929.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____7946
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____7956  -> Dummy :: env1)
                             env) in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____7972 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____7972
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____7985 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____8007  ->
                        match uu____8007 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____8046 =
                                let uu___170_8047 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___170_8047.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___170_8047.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____8046 in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos in
                            let memo = FStar_Util.mk_ref None in
                            let rec_env1 = (Clos (env, fix_f_i, memo, true))
                              :: rec_env in
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1")))) (snd lbs)
                   (env, [], (Prims.parse_int "0")) in
               (match uu____7985 with
                | (rec_env,memos,uu____8107) ->
                    let uu____8122 =
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
                             let uu____8164 =
                               let uu____8165 =
                                 let uu____8175 = FStar_Util.mk_ref None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____8175, false) in
                               Clos uu____8165 in
                             uu____8164 :: env1) (snd lbs) env in
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
                             FStar_Syntax_Syntax.tk = uu____8213;
                             FStar_Syntax_Syntax.pos = uu____8214;
                             FStar_Syntax_Syntax.vars = uu____8215;_},uu____8216,uu____8217))::uu____8218
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____8224 -> false in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____8231 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____8231
                        then
                          let uu___171_8232 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___171_8232.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps = (uu___171_8232.primitive_steps)
                          }
                        else
                          (let uu___172_8234 = cfg in
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___172_8234.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta];
                             primitive_steps =
                               (uu___172_8234.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____8236 =
                         let uu____8237 = FStar_Syntax_Subst.compress head1 in
                         uu____8237.FStar_Syntax_Syntax.n in
                       match uu____8236 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____8251 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8251 with
                            | (uu____8252,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____8256 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____8263 =
                                         let uu____8264 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____8264.FStar_Syntax_Syntax.n in
                                       match uu____8263 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____8269,uu____8270))
                                           ->
                                           let uu____8279 =
                                             let uu____8280 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____8280.FStar_Syntax_Syntax.n in
                                           (match uu____8279 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____8285,msrc,uu____8287))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____8296 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                Some uu____8296
                                            | uu____8297 -> None)
                                       | uu____8298 -> None in
                                     let uu____8299 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____8299 with
                                      | Some e ->
                                          let lb1 =
                                            let uu___173_8303 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___173_8303.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___173_8303.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___173_8303.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Syntax_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____8304 =
                                            FStar_List.tl stack1 in
                                          let uu____8305 =
                                            let uu____8306 =
                                              let uu____8309 =
                                                let uu____8310 =
                                                  let uu____8318 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____8318) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____8310 in
                                              FStar_Syntax_Syntax.mk
                                                uu____8309 in
                                            uu____8306 None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____8304 uu____8305
                                      | None  ->
                                          let uu____8335 =
                                            let uu____8336 = is_return body in
                                            match uu____8336 with
                                            | Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____8339;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____8340;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____8341;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____8346 -> false in
                                          if uu____8335
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
                                               let uu____8366 =
                                                 let uu____8369 =
                                                   let uu____8370 =
                                                     let uu____8385 =
                                                       let uu____8387 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____8387] in
                                                     (uu____8385, body1,
                                                       (Some
                                                          (FStar_Util.Inr
                                                             (m1, [])))) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____8370 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8369 in
                                               uu____8366 None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____8420 =
                                                 let uu____8421 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____8421.FStar_Syntax_Syntax.n in
                                               match uu____8420 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____8427::uu____8428::[])
                                                   ->
                                                   let uu____8434 =
                                                     let uu____8437 =
                                                       let uu____8438 =
                                                         let uu____8443 =
                                                           let uu____8445 =
                                                             let uu____8446 =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____8446 in
                                                           let uu____8447 =
                                                             let uu____8449 =
                                                               let uu____8450
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____8450 in
                                                             [uu____8449] in
                                                           uu____8445 ::
                                                             uu____8447 in
                                                         (bind1, uu____8443) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____8438 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8437 in
                                                   uu____8434 None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____8462 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____8468 =
                                                 let uu____8471 =
                                                   let uu____8472 =
                                                     let uu____8482 =
                                                       let uu____8484 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____8485 =
                                                         let uu____8487 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____8488 =
                                                           let uu____8490 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____8491 =
                                                             let uu____8493 =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____8494 =
                                                               let uu____8496
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____8497
                                                                 =
                                                                 let uu____8499
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____8499] in
                                                               uu____8496 ::
                                                                 uu____8497 in
                                                             uu____8493 ::
                                                               uu____8494 in
                                                           uu____8490 ::
                                                             uu____8491 in
                                                         uu____8487 ::
                                                           uu____8488 in
                                                       uu____8484 ::
                                                         uu____8485 in
                                                     (bind_inst, uu____8482) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____8472 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8471 in
                                               uu____8468 None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____8511 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____8511 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____8529 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8529 with
                            | (uu____8530,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____8553 =
                                        let uu____8554 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____8554.FStar_Syntax_Syntax.n in
                                      match uu____8553 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____8560) -> t4
                                      | uu____8565 -> head2 in
                                    let uu____8566 =
                                      let uu____8567 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____8567.FStar_Syntax_Syntax.n in
                                    match uu____8566 with
                                    | FStar_Syntax_Syntax.Tm_fvar x -> Some x
                                    | uu____8572 -> None in
                                  let uu____8573 = maybe_extract_fv head2 in
                                  match uu____8573 with
                                  | Some x when
                                      let uu____8579 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____8579
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____8583 =
                                          maybe_extract_fv head3 in
                                        match uu____8583 with
                                        | Some uu____8586 -> Some true
                                        | uu____8587 -> Some false in
                                      (head3, action_unfolded)
                                  | uu____8590 -> (head2, None) in
                                ((let is_arg_impure uu____8601 =
                                    match uu____8601 with
                                    | (e,q) ->
                                        let uu____8606 =
                                          let uu____8607 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____8607.FStar_Syntax_Syntax.n in
                                        (match uu____8606 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____8622 -> false) in
                                  let uu____8623 =
                                    let uu____8624 =
                                      let uu____8628 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____8628 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____8624 in
                                  if uu____8623
                                  then
                                    let uu____8631 =
                                      let uu____8632 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____8632 in
                                    failwith uu____8631
                                  else ());
                                 (let uu____8634 =
                                    maybe_unfold_action head_app in
                                  match uu____8634 with
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
                                      let uu____8669 = FStar_List.tl stack1 in
                                      norm cfg env uu____8669 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____8683 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____8683 in
                           let uu____8684 = FStar_List.tl stack1 in
                           norm cfg env uu____8684 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____8767  ->
                                     match uu____8767 with
                                     | (pat,wopt,tm) ->
                                         let uu____8805 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____8805))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____8831 = FStar_List.tl stack1 in
                           norm cfg env uu____8831 tm
                       | uu____8832 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.tk = uu____8841;
                             FStar_Syntax_Syntax.pos = uu____8842;
                             FStar_Syntax_Syntax.vars = uu____8843;_},uu____8844,uu____8845))::uu____8846
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____8852 -> false in
                    if should_reify
                    then
                      let uu____8853 = FStar_List.tl stack1 in
                      let uu____8854 =
                        let uu____8855 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____8855 in
                      norm cfg env uu____8853 uu____8854
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____8858 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____8858
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___174_8864 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___174_8864.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___174_8864.primitive_steps)
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
                | uu____8866 ->
                    (match stack1 with
                     | uu____8867::uu____8868 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____8872)
                              -> norm cfg env ((Meta (m, r)) :: stack1) head1
                          | FStar_Syntax_Syntax.Meta_pattern args ->
                              let args1 = norm_pattern_args cfg env args in
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_pattern args1),
                                      (t1.FStar_Syntax_Syntax.pos))) ::
                                stack1) head1
                          | uu____8887 -> norm cfg env stack1 head1)
                     | [] ->
                         let head2 = norm cfg env [] head1 in
                         let m1 =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               let uu____8897 =
                                 norm_pattern_args cfg env args in
                               FStar_Syntax_Syntax.Meta_pattern uu____8897
                           | uu____8904 -> m in
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
              let uu____8916 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____8916 with
              | (uu____8917,return_repr) ->
                  let return_inst =
                    let uu____8924 =
                      let uu____8925 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____8925.FStar_Syntax_Syntax.n in
                    match uu____8924 with
                    | FStar_Syntax_Syntax.Tm_uinst (return_tm,uu____8931::[])
                        ->
                        let uu____8937 =
                          let uu____8940 =
                            let uu____8941 =
                              let uu____8946 =
                                let uu____8948 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____8948] in
                              (return_tm, uu____8946) in
                            FStar_Syntax_Syntax.Tm_uinst uu____8941 in
                          FStar_Syntax_Syntax.mk uu____8940 in
                        uu____8937 None e.FStar_Syntax_Syntax.pos
                    | uu____8960 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____8963 =
                    let uu____8966 =
                      let uu____8967 =
                        let uu____8977 =
                          let uu____8979 = FStar_Syntax_Syntax.as_arg t in
                          let uu____8980 =
                            let uu____8982 = FStar_Syntax_Syntax.as_arg e in
                            [uu____8982] in
                          uu____8979 :: uu____8980 in
                        (return_inst, uu____8977) in
                      FStar_Syntax_Syntax.Tm_app uu____8967 in
                    FStar_Syntax_Syntax.mk uu____8966 in
                  uu____8963 None e.FStar_Syntax_Syntax.pos
            else
              (let uu____8995 = FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____8995 with
               | None  ->
                   let uu____8997 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____8997
               | Some
                   { FStar_TypeChecker_Env.msource = uu____8998;
                     FStar_TypeChecker_Env.mtarget = uu____8999;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____9000;
                         FStar_TypeChecker_Env.mlift_term = None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | Some
                   { FStar_TypeChecker_Env.msource = uu____9011;
                     FStar_TypeChecker_Env.mtarget = uu____9012;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____9013;
                         FStar_TypeChecker_Env.mlift_term = Some lift;_};_}
                   ->
                   let uu____9031 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____9031)
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
                (fun uu____9061  ->
                   match uu____9061 with
                   | (a,imp) ->
                       let uu____9068 = norm cfg env [] a in
                       (uu____9068, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___175_9083 = comp1 in
            let uu____9086 =
              let uu____9087 =
                let uu____9093 = norm cfg env [] t in
                let uu____9094 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____9093, uu____9094) in
              FStar_Syntax_Syntax.Total uu____9087 in
            {
              FStar_Syntax_Syntax.n = uu____9086;
              FStar_Syntax_Syntax.tk = (uu___175_9083.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___175_9083.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___175_9083.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___176_9109 = comp1 in
            let uu____9112 =
              let uu____9113 =
                let uu____9119 = norm cfg env [] t in
                let uu____9120 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____9119, uu____9120) in
              FStar_Syntax_Syntax.GTotal uu____9113 in
            {
              FStar_Syntax_Syntax.n = uu____9112;
              FStar_Syntax_Syntax.tk = (uu___176_9109.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___176_9109.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___176_9109.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____9151  ->
                      match uu____9151 with
                      | (a,i) ->
                          let uu____9158 = norm cfg env [] a in
                          (uu____9158, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___139_9163  ->
                      match uu___139_9163 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____9167 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____9167
                      | f -> f)) in
            let uu___177_9171 = comp1 in
            let uu____9174 =
              let uu____9175 =
                let uu___178_9176 = ct in
                let uu____9177 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____9178 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____9181 = norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____9177;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___178_9176.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____9178;
                  FStar_Syntax_Syntax.effect_args = uu____9181;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____9175 in
            {
              FStar_Syntax_Syntax.n = uu____9174;
              FStar_Syntax_Syntax.tk = (uu___177_9171.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___177_9171.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___177_9171.FStar_Syntax_Syntax.vars)
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
            (let uu___179_9198 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___179_9198.tcenv);
               delta_level = (uu___179_9198.delta_level);
               primitive_steps = (uu___179_9198.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____9203 = norm1 t in
          FStar_Syntax_Util.non_informative uu____9203 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____9206 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___180_9220 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.tk = (uu___180_9220.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___180_9220.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___180_9220.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____9230 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____9230
            then
              let ct1 =
                match downgrade_ghost_effect_name
                        ct.FStar_Syntax_Syntax.effect_name
                with
                | Some pure_eff ->
                    let uu___181_9235 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___181_9235.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___181_9235.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___181_9235.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___181_9235.FStar_Syntax_Syntax.flags)
                    }
                | None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___182_9237 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___182_9237.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Syntax_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___182_9237.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___182_9237.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___182_9237.FStar_Syntax_Syntax.flags)
                    } in
              let uu___183_9238 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.tk =
                  (uu___183_9238.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___183_9238.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___183_9238.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____9244 -> c
and norm_binder:
  cfg ->
    env ->
      FStar_Syntax_Syntax.binder ->
        (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  =
  fun cfg  ->
    fun env  ->
      fun uu____9247  ->
        match uu____9247 with
        | (x,imp) ->
            let uu____9250 =
              let uu___184_9251 = x in
              let uu____9252 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___184_9251.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___184_9251.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____9252
              } in
            (uu____9250, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____9258 =
          FStar_List.fold_left
            (fun uu____9265  ->
               fun b  ->
                 match uu____9265 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____9258 with | (nbs,uu____9282) -> FStar_List.rev nbs
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
            let uu____9299 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
            if uu____9299
            then
              let t = norm cfg env [] lc.FStar_Syntax_Syntax.res_typ in
              let uu____9304 = FStar_Syntax_Util.is_total_lcomp lc in
              (if uu____9304
               then
                 let uu____9308 =
                   let uu____9311 =
                     let uu____9312 =
                       let uu____9315 = FStar_Syntax_Syntax.mk_Total t in
                       FStar_Syntax_Util.comp_set_flags uu____9315 flags in
                     FStar_Syntax_Util.lcomp_of_comp uu____9312 in
                   FStar_Util.Inl uu____9311 in
                 Some uu____9308
               else
                 (let uu____9319 =
                    let uu____9322 =
                      let uu____9323 =
                        let uu____9326 = FStar_Syntax_Syntax.mk_GTotal t in
                        FStar_Syntax_Util.comp_set_flags uu____9326 flags in
                      FStar_Syntax_Util.lcomp_of_comp uu____9323 in
                    FStar_Util.Inl uu____9322 in
                  Some uu____9319))
            else
              Some
                (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags))
        | uu____9339 -> lopt
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
              ((let uu____9351 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____9351
                then
                  let uu____9352 = FStar_Syntax_Print.term_to_string tm in
                  let uu____9353 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2 "Normalized %s to %s\n" uu____9352
                    uu____9353
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___185_9364 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___185_9364.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____9384  ->
                    let uu____9385 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____9385);
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
              let uu____9422 =
                let uu___186_9423 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___186_9423.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___186_9423.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___186_9423.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____9422
          | (Arg (Univ uu____9428,uu____9429,uu____9430))::uu____9431 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____9433,uu____9434))::uu____9435 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____9447),aq,r))::stack2 ->
              (log cfg
                 (fun uu____9463  ->
                    let uu____9464 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____9464);
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
                 (let uu____9475 = FStar_ST.read m in
                  match uu____9475 with
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
                  | Some (uu____9501,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq) None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.extend_app head1 (t, aq) None r in
              let uu____9523 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____9523
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____9530  ->
                    let uu____9531 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____9531);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____9536 =
                  log cfg
                    (fun uu____9538  ->
                       let uu____9539 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____9540 =
                         let uu____9541 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____9548  ->
                                   match uu____9548 with
                                   | (p,uu____9554,uu____9555) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____9541
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____9539 uu____9540);
                  (let whnf = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___140_9565  ->
                               match uu___140_9565 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____9566 -> false)) in
                     let steps' =
                       let uu____9569 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____9569
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___187_9572 = cfg in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___187_9572.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___187_9572.primitive_steps)
                     } in
                   let norm_or_whnf env2 t1 =
                     if whnf
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____9606 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____9622 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____9656  ->
                                   fun uu____9657  ->
                                     match (uu____9656, uu____9657) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____9722 = norm_pat env3 p1 in
                                         (match uu____9722 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____9622 with
                          | (pats1,env3) ->
                              ((let uu___188_9788 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___188_9788.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___188_9788.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___189_9802 = x in
                           let uu____9803 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___189_9802.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___189_9802.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9803
                           } in
                         ((let uu___190_9809 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___190_9809.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___190_9809.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___191_9814 = x in
                           let uu____9815 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___191_9814.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___191_9814.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9815
                           } in
                         ((let uu___192_9821 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___192_9821.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___192_9821.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___193_9831 = x in
                           let uu____9832 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___193_9831.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___193_9831.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9832
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___194_9839 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.ty =
                               (uu___194_9839.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___194_9839.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf -> branches
                     | uu____9843 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____9846 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____9846 with
                                 | (p,wopt,e) ->
                                     let uu____9864 = norm_pat env1 p in
                                     (match uu____9864 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | None  -> None
                                            | Some w ->
                                                let uu____9888 =
                                                  norm_or_whnf env2 w in
                                                Some uu____9888 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____9893 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____9893) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____9903) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____9908 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____9909;
                        FStar_Syntax_Syntax.fv_delta = uu____9910;
                        FStar_Syntax_Syntax.fv_qual = Some
                          (FStar_Syntax_Syntax.Data_ctor );_}
                      -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____9914;
                        FStar_Syntax_Syntax.fv_delta = uu____9915;
                        FStar_Syntax_Syntax.fv_qual = Some
                          (FStar_Syntax_Syntax.Record_ctor uu____9916);_}
                      -> true
                  | uu____9923 -> false in
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
                  let uu____10022 =
                    FStar_Syntax_Util.head_and_args scrutinee2 in
                  match uu____10022 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var uu____10054 ->
                           FStar_Util.Inl [scrutinee2]
                       | FStar_Syntax_Syntax.Pat_wild uu____10056 ->
                           FStar_Util.Inl [scrutinee2]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____10058 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____10070 ->
                                let uu____10071 =
                                  let uu____10072 = is_cons head1 in
                                  Prims.op_Negation uu____10072 in
                                FStar_Util.Inr uu____10071)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____10086 =
                             let uu____10087 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____10087.FStar_Syntax_Syntax.n in
                           (match uu____10086 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____10094 ->
                                let uu____10095 =
                                  let uu____10096 = is_cons head1 in
                                  Prims.op_Negation uu____10096 in
                                FStar_Util.Inr uu____10095))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____10130)::rest_a,(p1,uu____10133)::rest_p) ->
                      let uu____10161 = matches_pat t1 p1 in
                      (match uu____10161 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____10175 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____10246 = matches_pat scrutinee1 p1 in
                      (match uu____10246 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____10256  ->
                                 let uu____10257 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____10258 =
                                   let uu____10259 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____10259
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____10257 uu____10258);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____10268 =
                                        let uu____10269 =
                                          let uu____10279 =
                                            FStar_Util.mk_ref (Some ([], t1)) in
                                          ([], t1, uu____10279, false) in
                                        Clos uu____10269 in
                                      uu____10268 :: env2) env1 s in
                             let uu____10302 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____10302))) in
                let uu____10303 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____10303
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___141_10317  ->
                match uu___141_10317 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | uu____10320 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____10324 -> d in
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
            let uu___195_10344 = config s e in
            {
              steps = (uu___195_10344.steps);
              tcenv = (uu___195_10344.tcenv);
              delta_level = (uu___195_10344.delta_level);
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
      fun t  -> let uu____10363 = config s e in norm_comp uu____10363 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____10370 = config [] env in norm_universe uu____10370 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun c  ->
      let uu____10377 = config [] env in ghost_to_pure_aux uu____10377 [] c
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
        let uu____10389 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____10389 in
      let uu____10390 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____10390
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | Some pure_eff ->
            let uu___196_10392 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___196_10392.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___196_10392.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____10393  ->
                    let uu____10394 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____10394))
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
            ((let uu____10407 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10407);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____10416 = config [AllowUnboundUniverses] env in
          norm_comp uu____10416 [] c
        with
        | e ->
            ((let uu____10420 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10420);
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
                   let uu____10457 =
                     let uu____10458 =
                       let uu____10463 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____10463) in
                     FStar_Syntax_Syntax.Tm_refine uu____10458 in
                   mk uu____10457 t01.FStar_Syntax_Syntax.pos
               | uu____10468 -> t2)
          | uu____10469 -> t2 in
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
        let uu____10491 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____10491 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____10507 ->
                 let uu____10511 = FStar_Syntax_Util.abs_formals e in
                 (match uu____10511 with
                  | (actuals,uu____10522,uu____10523) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____10545 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____10545 with
                         | (binders,args) ->
                             let uu____10555 =
                               FStar_Syntax_Syntax.mk_Tm_app e args None
                                 e.FStar_Syntax_Syntax.pos in
                             let uu____10558 =
                               let uu____10565 =
                                 FStar_All.pipe_right
                                   (FStar_Syntax_Util.lcomp_of_comp c)
                                   (fun _0_44  -> FStar_Util.Inl _0_44) in
                               FStar_All.pipe_right uu____10565
                                 (fun _0_45  -> Some _0_45) in
                             FStar_Syntax_Util.abs binders uu____10555
                               uu____10558)))
let eta_expand:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____10601 =
        let uu____10605 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
        (uu____10605, (t.FStar_Syntax_Syntax.n)) in
      match uu____10601 with
      | (Some sort,uu____10612) ->
          let uu____10614 = mk sort t.FStar_Syntax_Syntax.pos in
          eta_expand_with_type env t uu____10614
      | (uu____10615,FStar_Syntax_Syntax.Tm_name x) ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____10619 ->
          let uu____10623 = FStar_Syntax_Util.head_and_args t in
          (match uu____10623 with
           | (head1,args) ->
               let uu____10649 =
                 let uu____10650 = FStar_Syntax_Subst.compress head1 in
                 uu____10650.FStar_Syntax_Syntax.n in
               (match uu____10649 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____10653,thead) ->
                    let uu____10671 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____10671 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____10702 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___201_10706 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___201_10706.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___201_10706.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___201_10706.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___201_10706.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___201_10706.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___201_10706.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ = None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___201_10706.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___201_10706.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___201_10706.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___201_10706.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___201_10706.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___201_10706.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___201_10706.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___201_10706.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___201_10706.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___201_10706.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___201_10706.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___201_10706.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___201_10706.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___201_10706.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___201_10706.FStar_TypeChecker_Env.qname_and_index)
                                 }) t in
                            match uu____10702 with
                            | (uu____10707,ty,uu____10709) ->
                                eta_expand_with_type env t ty))
                | uu____10710 ->
                    let uu____10711 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___202_10715 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___202_10715.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___202_10715.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___202_10715.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___202_10715.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___202_10715.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___202_10715.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ = None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___202_10715.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___202_10715.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___202_10715.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___202_10715.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___202_10715.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___202_10715.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___202_10715.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___202_10715.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___202_10715.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___202_10715.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___202_10715.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___202_10715.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___202_10715.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___202_10715.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___202_10715.FStar_TypeChecker_Env.qname_and_index)
                         }) t in
                    (match uu____10711 with
                     | (uu____10716,ty,uu____10718) ->
                         eta_expand_with_type env t ty)))
let elim_uvars_aux_tc:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.comp) FStar_Util.either
          ->
          (FStar_Syntax_Syntax.univ_names* (FStar_Syntax_Syntax.bv*
            FStar_Syntax_Syntax.aqual) Prims.list*
            (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.comp',Prims.unit)
                                        FStar_Syntax_Syntax.syntax)
            FStar_Util.either)
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun tc  ->
          let t =
            match (binders, tc) with
            | ([],FStar_Util.Inl t) -> t
            | ([],FStar_Util.Inr c) ->
                failwith "Impossible: empty bindes with a comp"
            | (uu____10764,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c)) None
                  c.FStar_Syntax_Syntax.pos
            | (uu____10772,FStar_Util.Inl t) ->
                let uu____10776 =
                  let uu____10779 =
                    let uu____10780 =
                      let uu____10788 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____10788) in
                    FStar_Syntax_Syntax.Tm_arrow uu____10780 in
                  FStar_Syntax_Syntax.mk uu____10779 in
                uu____10776 None t.FStar_Syntax_Syntax.pos in
          let uu____10797 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____10797 with
          | (univ_names1,t1) ->
              let t2 = reduce_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____10814 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____10846 ->
                    let uu____10847 =
                      let uu____10852 =
                        let uu____10853 = FStar_Syntax_Subst.compress t3 in
                        uu____10853.FStar_Syntax_Syntax.n in
                      (uu____10852, tc) in
                    (match uu____10847 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____10869) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____10893) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____10919,FStar_Util.Inl uu____10920) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____10934 -> failwith "Impossible") in
              (match uu____10814 with
               | (binders1,tc1) -> (univ_names1, binders1, tc1))
let elim_uvars_aux_t:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.univ_names* (FStar_Syntax_Syntax.bv*
            FStar_Syntax_Syntax.aqual) Prims.list* FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun t  ->
          let uu____10999 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____10999 with
          | (univ_names1,binders1,tc) ->
              let uu____11033 = FStar_Util.left tc in
              (univ_names1, binders1, uu____11033)
let elim_uvars_aux_c:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.univ_names* (FStar_Syntax_Syntax.bv*
            FStar_Syntax_Syntax.aqual) Prims.list*
            (FStar_Syntax_Syntax.comp',Prims.unit)
            FStar_Syntax_Syntax.syntax)
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun c  ->
          let uu____11059 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____11059 with
          | (univ_names1,binders1,tc) ->
              let uu____11095 = FStar_Util.right tc in
              (univ_names1, binders1, uu____11095)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____11121 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____11121 with
           | (univ_names1,binders1,typ1) ->
               let uu___203_11137 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___203_11137.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___203_11137.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___203_11137.FStar_Syntax_Syntax.sigmeta)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___204_11149 = s in
          let uu____11150 =
            let uu____11151 =
              let uu____11156 = FStar_List.map (elim_uvars env) sigs in
              (uu____11156, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____11151 in
          {
            FStar_Syntax_Syntax.sigel = uu____11150;
            FStar_Syntax_Syntax.sigrng =
              (uu___204_11149.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___204_11149.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___204_11149.FStar_Syntax_Syntax.sigmeta)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____11168 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____11168 with
           | (univ_names1,uu____11178,typ1) ->
               let uu___205_11186 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___205_11186.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___205_11186.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___205_11186.FStar_Syntax_Syntax.sigmeta)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____11191 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____11191 with
           | (univ_names1,uu____11201,typ1) ->
               let uu___206_11209 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___206_11209.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___206_11209.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___206_11209.FStar_Syntax_Syntax.sigmeta)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids,attrs) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____11228 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____11228 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____11243 =
                            let uu____11244 =
                              FStar_Syntax_Subst.subst opening t in
                            reduce_uvar_solutions env uu____11244 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____11243 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___207_11247 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___207_11247.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___207_11247.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___208_11248 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids, attrs));
            FStar_Syntax_Syntax.sigrng =
              (uu___208_11248.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___208_11248.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___208_11248.FStar_Syntax_Syntax.sigmeta)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___209_11256 = s in
          let uu____11257 =
            let uu____11258 = reduce_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____11258 in
          {
            FStar_Syntax_Syntax.sigel = uu____11257;
            FStar_Syntax_Syntax.sigrng =
              (uu___209_11256.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___209_11256.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___209_11256.FStar_Syntax_Syntax.sigmeta)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____11262 = elim_uvars_aux_t env us [] t in
          (match uu____11262 with
           | (us1,uu____11272,t1) ->
               let uu___210_11280 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___210_11280.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___210_11280.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___210_11280.FStar_Syntax_Syntax.sigmeta)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11281 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____11283 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____11283 with
           | (univs1,binders,signature) ->
               let uu____11299 =
                 let uu____11304 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____11304 with
                 | (univs_opening,univs2) ->
                     let uu____11319 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____11319) in
               (match uu____11299 with
                | (univs_opening,univs_closing) ->
                    let uu____11329 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____11333 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____11334 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____11333, uu____11334) in
                    (match uu____11329 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____11351 =
                           match uu____11351 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____11363 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____11363 with
                                | (us1,t1) ->
                                    let uu____11370 =
                                      let uu____11373 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____11377 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____11373, uu____11377) in
                                    (match uu____11370 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____11385 =
                                           let uu____11388 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____11393 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____11388, uu____11393) in
                                         (match uu____11385 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____11403 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____11403 in
                                              let uu____11404 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____11404 with
                                               | (uu____11415,uu____11416,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____11425 =
                                                       let uu____11426 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____11426 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____11425 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____11431 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____11431 with
                           | (uu____11438,uu____11439,t1) -> t1 in
                         let elim_action a =
                           let action_typ_templ =
                             (FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_ascribed
                                   ((a.FStar_Syntax_Syntax.action_defn),
                                     ((FStar_Util.Inl
                                         (a.FStar_Syntax_Syntax.action_typ)),
                                       None), None))) None
                               (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_typ_templ t =
                             let uu____11493 =
                               let uu____11494 =
                                 FStar_Syntax_Subst.compress t in
                               uu____11494.FStar_Syntax_Syntax.n in
                             match uu____11493 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl typ,None ),None ) ->
                                 (defn, typ)
                             | uu____11542 -> failwith "Impossible" in
                           let uu____11549 =
                             elim_uvars_aux_t env
                               (FStar_List.append univs1
                                  a.FStar_Syntax_Syntax.action_univs)
                               (FStar_List.append binders
                                  a.FStar_Syntax_Syntax.action_params)
                               action_typ_templ in
                           match uu____11549 with
                           | (u_action_univs,b_action_params,res) ->
                               let action_univs =
                                 FStar_Util.nth_tail n1 u_action_univs in
                               let action_params =
                                 FStar_Util.nth_tail
                                   (FStar_List.length binders)
                                   b_action_params in
                               let uu____11581 =
                                 destruct_action_typ_templ res in
                               (match uu____11581 with
                                | (action_defn,action_typ) ->
                                    let uu___211_11598 = a in
                                    {
                                      FStar_Syntax_Syntax.action_name =
                                        (uu___211_11598.FStar_Syntax_Syntax.action_name);
                                      FStar_Syntax_Syntax.action_unqualified_name
                                        =
                                        (uu___211_11598.FStar_Syntax_Syntax.action_unqualified_name);
                                      FStar_Syntax_Syntax.action_univs =
                                        action_univs;
                                      FStar_Syntax_Syntax.action_params =
                                        action_params;
                                      FStar_Syntax_Syntax.action_defn =
                                        action_defn;
                                      FStar_Syntax_Syntax.action_typ =
                                        action_typ
                                    }) in
                         let ed1 =
                           let uu___212_11600 = ed in
                           let uu____11601 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____11602 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____11603 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____11604 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____11605 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____11606 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____11607 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____11608 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____11609 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____11610 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____11611 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____11612 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____11613 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____11614 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___212_11600.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___212_11600.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____11601;
                             FStar_Syntax_Syntax.bind_wp = uu____11602;
                             FStar_Syntax_Syntax.if_then_else = uu____11603;
                             FStar_Syntax_Syntax.ite_wp = uu____11604;
                             FStar_Syntax_Syntax.stronger = uu____11605;
                             FStar_Syntax_Syntax.close_wp = uu____11606;
                             FStar_Syntax_Syntax.assert_p = uu____11607;
                             FStar_Syntax_Syntax.assume_p = uu____11608;
                             FStar_Syntax_Syntax.null_wp = uu____11609;
                             FStar_Syntax_Syntax.trivial = uu____11610;
                             FStar_Syntax_Syntax.repr = uu____11611;
                             FStar_Syntax_Syntax.return_repr = uu____11612;
                             FStar_Syntax_Syntax.bind_repr = uu____11613;
                             FStar_Syntax_Syntax.actions = uu____11614
                           } in
                         let uu___213_11616 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___213_11616.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___213_11616.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___213_11616.FStar_Syntax_Syntax.sigmeta)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___142_11627 =
            match uu___142_11627 with
            | None  -> None
            | Some (us,t) ->
                let uu____11642 = elim_uvars_aux_t env us [] t in
                (match uu____11642 with
                 | (us1,uu____11655,t1) -> Some (us1, t1)) in
          let sub_eff1 =
            let uu___214_11666 = sub_eff in
            let uu____11667 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____11669 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___214_11666.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___214_11666.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____11667;
              FStar_Syntax_Syntax.lift = uu____11669
            } in
          let uu___215_11671 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___215_11671.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___215_11671.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___215_11671.FStar_Syntax_Syntax.sigmeta)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____11679 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____11679 with
           | (univ_names1,binders1,comp1) ->
               let uu___216_11701 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___216_11701.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___216_11701.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___216_11701.FStar_Syntax_Syntax.sigmeta)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____11708 -> s