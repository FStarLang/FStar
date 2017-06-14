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
              | FStar_Syntax_Syntax.Tm_unknown  ->
                  (FStar_ST.write t1.FStar_Syntax_Syntax.tk None; t1)
              | FStar_Syntax_Syntax.Tm_constant uu____1061 ->
                  (FStar_ST.write t1.FStar_Syntax_Syntax.tk None; t1)
              | FStar_Syntax_Syntax.Tm_name uu____1066 ->
                  (FStar_ST.write t1.FStar_Syntax_Syntax.tk None; t1)
              | FStar_Syntax_Syntax.Tm_fvar uu____1071 ->
                  (FStar_ST.write t1.FStar_Syntax_Syntax.tk None; t1)
              | FStar_Syntax_Syntax.Tm_uvar uu____1076 -> t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____1088 =
                    let uu____1089 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____1089 in
                  mk uu____1088 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t2,us) ->
                  let uu____1096 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t2 uu____1096
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____1098 = lookup_bvar env x in
                  (match uu____1098 with
                   | Univ uu____1099 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____1103) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____1171 = closures_as_binders_delayed cfg env bs in
                  (match uu____1171 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____1191 =
                         let uu____1192 =
                           let uu____1207 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____1207) in
                         FStar_Syntax_Syntax.Tm_abs uu____1192 in
                       mk uu____1191 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____1237 = closures_as_binders_delayed cfg env bs in
                  (match uu____1237 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____1268 =
                    let uu____1275 =
                      let uu____1279 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____1279] in
                    closures_as_binders_delayed cfg env uu____1275 in
                  (match uu____1268 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____1293 =
                         let uu____1294 =
                           let uu____1299 =
                             let uu____1300 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____1300
                               FStar_Pervasives.fst in
                           (uu____1299, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____1294 in
                       mk uu____1293 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____1368 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____1368
                    | FStar_Util.Inr c ->
                        let uu____1382 = close_comp cfg env c in
                        FStar_Util.Inr uu____1382 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____1397 =
                    let uu____1398 =
                      let uu____1416 = closure_as_term_delayed cfg env t11 in
                      (uu____1416, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____1398 in
                  mk uu____1397 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____1454 =
                    let uu____1455 =
                      let uu____1460 = closure_as_term_delayed cfg env t' in
                      let uu____1463 =
                        let uu____1464 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____1464 in
                      (uu____1460, uu____1463) in
                    FStar_Syntax_Syntax.Tm_meta uu____1455 in
                  mk uu____1454 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____1506 =
                    let uu____1507 =
                      let uu____1512 = closure_as_term_delayed cfg env t' in
                      let uu____1515 =
                        let uu____1516 =
                          let uu____1521 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____1521) in
                        FStar_Syntax_Syntax.Meta_monadic uu____1516 in
                      (uu____1512, uu____1515) in
                    FStar_Syntax_Syntax.Tm_meta uu____1507 in
                  mk uu____1506 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____1540 =
                    let uu____1541 =
                      let uu____1546 = closure_as_term_delayed cfg env t' in
                      let uu____1549 =
                        let uu____1550 =
                          let uu____1556 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____1556) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____1550 in
                      (uu____1546, uu____1549) in
                    FStar_Syntax_Syntax.Tm_meta uu____1541 in
                  mk uu____1540 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____1569 =
                    let uu____1570 =
                      let uu____1575 = closure_as_term_delayed cfg env t' in
                      (uu____1575, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____1570 in
                  mk uu____1569 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____1596  -> Dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let body1 =
                    match lb.FStar_Syntax_Syntax.lbname with
                    | FStar_Util.Inr uu____1607 -> body
                    | FStar_Util.Inl uu____1608 ->
                        closure_as_term cfg (Dummy :: env0) body in
                  let lb1 =
                    let uu___147_1610 = lb in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___147_1610.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___147_1610.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = typ;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___147_1610.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = def
                    } in
                  mk (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((uu____1617,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____1641  -> fun env2  -> Dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____1646 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____1646
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____1650  -> fun env2  -> Dummy :: env2) lbs
                          env_univs in
                    let uu___148_1653 = lb in
                    let uu____1654 =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let uu____1657 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___148_1653.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___148_1653.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = uu____1654;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___148_1653.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____1657
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____1668  -> fun env1  -> Dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____1719 =
                    match uu____1719 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____1757 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____1770 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____1799  ->
                                        fun uu____1800  ->
                                          match (uu____1799, uu____1800) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____1854 =
                                                norm_pat env3 p1 in
                                              (match uu____1854 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____1770 with
                               | (pats1,env3) ->
                                   ((let uu___149_1907 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___149_1907.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___150_1918 = x in
                                let uu____1919 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___150_1918.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___150_1918.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1919
                                } in
                              ((let uu___151_1924 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___151_1924.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___152_1928 = x in
                                let uu____1929 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___152_1928.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___152_1928.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1929
                                } in
                              ((let uu___153_1934 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___153_1934.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___154_1943 = x in
                                let uu____1944 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___154_1943.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___154_1943.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1944
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___155_1950 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___155_1950.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____1952 = norm_pat env1 pat in
                        (match uu____1952 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | None  -> None
                               | Some w ->
                                   let uu____1972 =
                                     closure_as_term cfg env2 w in
                                   Some uu____1972 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____1976 =
                    let uu____1977 =
                      let uu____1992 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____1992) in
                    FStar_Syntax_Syntax.Tm_match uu____1977 in
                  mk uu____1976 t1.FStar_Syntax_Syntax.pos))
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
        | uu____2039 -> closure_as_term cfg env t
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
        | uu____2055 ->
            FStar_List.map
              (fun uu____2065  ->
                 match uu____2065 with
                 | (x,imp) ->
                     let uu____2080 = closure_as_term_delayed cfg env x in
                     (uu____2080, imp)) args
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
        let uu____2092 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____2116  ->
                  fun uu____2117  ->
                    match (uu____2116, uu____2117) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___156_2161 = b in
                          let uu____2162 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___156_2161.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___156_2161.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____2162
                          } in
                        let env2 = Dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____2092 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____2209 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____2221 = closure_as_term_delayed cfg env t in
                 let uu____2222 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____2221 uu____2222
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____2232 = closure_as_term_delayed cfg env t in
                 let uu____2233 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____2232 uu____2233
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
                        (fun uu___134_2249  ->
                           match uu___134_2249 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____2253 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____2253
                           | f -> f)) in
                 let uu____2257 =
                   let uu___157_2258 = c1 in
                   let uu____2259 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____2259;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___157_2258.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____2257)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.cflags Prims.list =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_List.filter
         (fun uu___135_2263  ->
            match uu___135_2263 with
            | FStar_Syntax_Syntax.DECREASES uu____2264 -> false
            | uu____2267 -> true))
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
            let uu____2295 = FStar_Syntax_Util.is_total_lcomp lc in
            if uu____2295
            then
              Some
                (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, flags))
            else
              (let uu____2312 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
               if uu____2312
               then
                 Some
                   (FStar_Util.Inr
                      (FStar_Syntax_Const.effect_GTot_lid, flags))
               else
                 Some
                   (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags)))
        | uu____2338 -> lopt
let built_in_primitive_steps: primitive_step Prims.list =
  let const_as_tm c p = mk (FStar_Syntax_Syntax.Tm_constant c) p in
  let int_as_const p i =
    let uu____2362 =
      let uu____2363 =
        let uu____2369 = FStar_Util.string_of_int i in (uu____2369, None) in
      FStar_Const.Const_int uu____2363 in
    const_as_tm uu____2362 p in
  let bool_as_const p b = const_as_tm (FStar_Const.Const_bool b) p in
  let string_as_const p b =
    const_as_tm
      (FStar_Const.Const_string ((FStar_Util.bytes_of_string b), p)) p in
  let arg_as_int uu____2396 =
    match uu____2396 with
    | (a,uu____2401) ->
        let uu____2403 =
          let uu____2404 = FStar_Syntax_Subst.compress a in
          uu____2404.FStar_Syntax_Syntax.n in
        (match uu____2403 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i,None ))
             ->
             let uu____2414 = FStar_Util.int_of_string i in Some uu____2414
         | uu____2415 -> None) in
  let arg_as_bounded_int uu____2424 =
    match uu____2424 with
    | (a,uu____2431) ->
        let uu____2435 =
          let uu____2436 = FStar_Syntax_Subst.compress a in
          uu____2436.FStar_Syntax_Syntax.n in
        (match uu____2435 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.tk = uu____2443;
                FStar_Syntax_Syntax.pos = uu____2444;
                FStar_Syntax_Syntax.vars = uu____2445;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,None ));
                                                            FStar_Syntax_Syntax.tk
                                                              = uu____2447;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____2448;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____2449;_},uu____2450)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____2477 =
               let uu____2480 = FStar_Util.int_of_string i in
               (fv1, uu____2480) in
             Some uu____2477
         | uu____2483 -> None) in
  let arg_as_bool uu____2492 =
    match uu____2492 with
    | (a,uu____2497) ->
        let uu____2499 =
          let uu____2500 = FStar_Syntax_Subst.compress a in
          uu____2500.FStar_Syntax_Syntax.n in
        (match uu____2499 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
             Some b
         | uu____2505 -> None) in
  let arg_as_char uu____2512 =
    match uu____2512 with
    | (a,uu____2517) ->
        let uu____2519 =
          let uu____2520 = FStar_Syntax_Subst.compress a in
          uu____2520.FStar_Syntax_Syntax.n in
        (match uu____2519 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
             Some c
         | uu____2525 -> None) in
  let arg_as_string uu____2532 =
    match uu____2532 with
    | (a,uu____2537) ->
        let uu____2539 =
          let uu____2540 = FStar_Syntax_Subst.compress a in
          uu____2540.FStar_Syntax_Syntax.n in
        (match uu____2539 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (bytes,uu____2545)) -> Some (FStar_Util.string_of_bytes bytes)
         | uu____2548 -> None) in
  let arg_as_list f uu____2569 =
    match uu____2569 with
    | (a,uu____2578) ->
        let rec sequence l =
          match l with
          | [] -> Some []
          | (None )::uu____2597 -> None
          | (Some x)::xs ->
              let uu____2607 = sequence xs in
              (match uu____2607 with
               | None  -> None
               | Some xs' -> Some (x :: xs')) in
        let uu____2618 = FStar_Syntax_Util.list_elements a in
        (match uu____2618 with
         | None  -> None
         | Some elts ->
             let uu____2628 =
               FStar_List.map
                 (fun x  ->
                    let uu____2633 = FStar_Syntax_Syntax.as_arg x in
                    f uu____2633) elts in
             sequence uu____2628) in
  let lift_unary f aopts =
    match aopts with
    | (Some a)::[] -> let uu____2663 = f a in Some uu____2663
    | uu____2664 -> None in
  let lift_binary f aopts =
    match aopts with
    | (Some a0)::(Some a1)::[] -> let uu____2703 = f a0 a1 in Some uu____2703
    | uu____2704 -> None in
  let unary_op as_a f r args =
    let uu____2748 = FStar_List.map as_a args in lift_unary (f r) uu____2748 in
  let binary_op as_a f r args =
    let uu____2798 = FStar_List.map as_a args in lift_binary (f r) uu____2798 in
  let as_primitive_step uu____2815 =
    match uu____2815 with
    | (l,arity,f) ->
        { name = l; arity; strong_reduction_ok = true; interpretation = f } in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  -> fun x  -> let uu____2853 = f x in int_as_const r uu____2853) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2876 = f x y in int_as_const r uu____2876) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  -> fun x  -> let uu____2893 = f x in bool_as_const r uu____2893) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2916 = f x y in bool_as_const r uu____2916) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2939 = f x y in string_as_const r uu____2939) in
  let list_of_string' rng s =
    let name l =
      let uu____2953 =
        let uu____2954 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            None in
        FStar_Syntax_Syntax.Tm_fvar uu____2954 in
      mk uu____2953 rng in
    let char_t = name FStar_Syntax_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____2964 =
      let uu____2966 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____2966 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____2964 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Const.exp_string s in
  let string_of_int1 rng i =
    let uu____2988 = FStar_Util.string_of_int i in
    string_as_const rng uu____2988 in
  let string_of_bool1 rng b =
    string_as_const rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____3004 = FStar_Util.string_of_int i in
    string_as_const rng uu____3004 in
  let string_of_bool2 rng b =
    string_as_const rng (if b then "true" else "false") in
  let basic_ops =
    let uu____3023 =
      let uu____3033 =
        let uu____3043 =
          let uu____3053 =
            let uu____3063 =
              let uu____3073 =
                let uu____3083 =
                  let uu____3093 =
                    let uu____3103 =
                      let uu____3113 =
                        let uu____3123 =
                          let uu____3133 =
                            let uu____3143 =
                              let uu____3153 =
                                let uu____3163 =
                                  let uu____3173 =
                                    let uu____3183 =
                                      let uu____3192 =
                                        FStar_Syntax_Const.p2l
                                          ["FStar";
                                          "String";
                                          "list_of_string"] in
                                      (uu____3192, (Prims.parse_int "1"),
                                        (unary_op arg_as_string
                                           list_of_string')) in
                                    let uu____3198 =
                                      let uu____3208 =
                                        let uu____3217 =
                                          FStar_Syntax_Const.p2l
                                            ["FStar";
                                            "String";
                                            "string_of_list"] in
                                        (uu____3217, (Prims.parse_int "1"),
                                          (unary_op (arg_as_list arg_as_char)
                                             string_of_list')) in
                                      [uu____3208] in
                                    uu____3183 :: uu____3198 in
                                  (FStar_Syntax_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_bool string_of_bool2))
                                    :: uu____3173 in
                                (FStar_Syntax_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (unary_op arg_as_int string_of_int2)) ::
                                  uu____3163 in
                              (FStar_Syntax_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____3153 in
                            (FStar_Syntax_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____3143 in
                          (FStar_Syntax_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____3133 in
                        (FStar_Syntax_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____3123 in
                      (FStar_Syntax_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____3113 in
                    (FStar_Syntax_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
                      :: uu____3103 in
                  (FStar_Syntax_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____3093 in
                (FStar_Syntax_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____3083 in
              (FStar_Syntax_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____3073 in
            (FStar_Syntax_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____3063 in
          (FStar_Syntax_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____3053 in
        (FStar_Syntax_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____3043 in
      (FStar_Syntax_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____3033 in
    (FStar_Syntax_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____3023 in
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
      let uu____3512 =
        let uu____3513 =
          let uu____3514 = FStar_Syntax_Syntax.as_arg c in [uu____3514] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____3513 in
      uu____3512 None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____3538 =
              let uu____3547 = FStar_Syntax_Const.p2l ["FStar"; m; "add"] in
              (uu____3547, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____3556  ->
                        fun uu____3557  ->
                          match (uu____3556, uu____3557) with
                          | ((int_to_t1,x),(uu____3568,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____3574 =
              let uu____3584 =
                let uu____3593 = FStar_Syntax_Const.p2l ["FStar"; m; "sub"] in
                (uu____3593, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____3602  ->
                          fun uu____3603  ->
                            match (uu____3602, uu____3603) with
                            | ((int_to_t1,x),(uu____3614,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____3620 =
                let uu____3630 =
                  let uu____3639 = FStar_Syntax_Const.p2l ["FStar"; m; "mul"] in
                  (uu____3639, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____3648  ->
                            fun uu____3649  ->
                              match (uu____3648, uu____3649) with
                              | ((int_to_t1,x),(uu____3660,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____3630] in
              uu____3584 :: uu____3620 in
            uu____3538 :: uu____3574)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_bool rng args =
    match args with
    | (_typ,uu____3726)::(a1,uu____3728)::(a2,uu____3730)::[] ->
        let uu____3759 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3759 with
         | FStar_Syntax_Util.Equal  ->
             let uu____3761 =
               mk
                 (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_bool true)) rng in
             Some uu____3761
         | FStar_Syntax_Util.NotEqual  ->
             let uu____3766 =
               mk
                 (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_bool false)) rng in
             Some uu____3766
         | uu____3771 -> None)
    | uu____3772 -> failwith "Unexpected number of arguments" in
  let interp_prop r args =
    match args with
    | (_typ,uu____3785)::(a1,uu____3787)::(a2,uu____3789)::[] ->
        let uu____3818 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3818 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___158_3822 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___158_3822.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___158_3822.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___158_3822.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___159_3829 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___159_3829.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___159_3829.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___159_3829.FStar_Syntax_Syntax.vars)
                })
         | uu____3834 -> None)
    | (_typ,uu____3836)::uu____3837::(a1,uu____3839)::(a2,uu____3841)::[] ->
        let uu____3878 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3878 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___158_3882 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___158_3882.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___158_3882.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___158_3882.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___159_3889 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___159_3889.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___159_3889.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___159_3889.FStar_Syntax_Syntax.vars)
                })
         | uu____3894 -> None)
    | uu____3895 -> failwith "Unexpected number of arguments" in
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
      let uu____3906 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops cfg.steps) in
      if uu____3906
      then tm
      else
        (let uu____3908 = FStar_Syntax_Util.head_and_args tm in
         match uu____3908 with
         | (head1,args) ->
             let uu____3934 =
               let uu____3935 = FStar_Syntax_Util.un_uinst head1 in
               uu____3935.FStar_Syntax_Syntax.n in
             (match uu____3934 with
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____3939 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps in
                  (match uu____3939 with
                   | None  -> tm
                   | Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then tm
                       else
                         (let uu____3951 =
                            prim_step.interpretation
                              head1.FStar_Syntax_Syntax.pos args in
                          match uu____3951 with
                          | None  -> tm
                          | Some reduced -> reduced))
              | uu____3954 -> tm))
let reduce_equality:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___160_3961 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___160_3961.tcenv);
           delta_level = (uu___160_3961.delta_level);
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
        let uu___161_3983 = t in
        {
          FStar_Syntax_Syntax.n = (uu___161_3983.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___161_3983.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___161_3983.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid ->
            Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid ->
            Some false
        | uu____4002 -> None in
      let simplify arg = ((simp_t (fst arg)), arg) in
      let uu____4029 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps) in
      if uu____4029
      then reduce_primops cfg tm
      else
        (match tm.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.tk = uu____4032;
                     FStar_Syntax_Syntax.pos = uu____4033;
                     FStar_Syntax_Syntax.vars = uu____4034;_},uu____4035);
                FStar_Syntax_Syntax.tk = uu____4036;
                FStar_Syntax_Syntax.pos = uu____4037;
                FStar_Syntax_Syntax.vars = uu____4038;_},args)
             ->
             let uu____4058 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____4058
             then
               let uu____4059 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____4059 with
                | (Some (true ),uu____4092)::(uu____4093,(arg,uu____4095))::[]
                    -> arg
                | (uu____4136,(arg,uu____4138))::(Some (true ),uu____4139)::[]
                    -> arg
                | (Some (false ),uu____4180)::uu____4181::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4219::(Some (false ),uu____4220)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4258 -> tm)
             else
               (let uu____4268 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____4268
                then
                  let uu____4269 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____4269 with
                  | (Some (true ),uu____4302)::uu____4303::[] ->
                      w FStar_Syntax_Util.t_true
                  | uu____4341::(Some (true ),uu____4342)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),uu____4380)::(uu____4381,(arg,uu____4383))::[]
                      -> arg
                  | (uu____4424,(arg,uu____4426))::(Some (false ),uu____4427)::[]
                      -> arg
                  | uu____4468 -> tm
                else
                  (let uu____4478 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____4478
                   then
                     let uu____4479 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____4479 with
                     | uu____4512::(Some (true ),uu____4513)::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (false ),uu____4551)::uu____4552::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____4590)::(uu____4591,(arg,uu____4593))::[]
                         -> arg
                     | uu____4634 -> tm
                   else
                     (let uu____4644 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____4644
                      then
                        let uu____4645 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____4645 with
                        | (Some (true ),uu____4678)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____4702)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____4726 -> tm
                      else
                        (let uu____4736 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid in
                         if uu____4736
                         then
                           match args with
                           | (t,uu____4738)::[] ->
                               let uu____4751 =
                                 let uu____4752 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____4752.FStar_Syntax_Syntax.n in
                               (match uu____4751 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____4755::[],body,uu____4757) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____4783 -> tm)
                                | uu____4785 -> tm)
                           | (uu____4786,Some (FStar_Syntax_Syntax.Implicit
                              uu____4787))::(t,uu____4789)::[] ->
                               let uu____4816 =
                                 let uu____4817 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____4817.FStar_Syntax_Syntax.n in
                               (match uu____4816 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____4820::[],body,uu____4822) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____4848 -> tm)
                                | uu____4850 -> tm)
                           | uu____4851 -> tm
                         else
                           (let uu____4858 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid in
                            if uu____4858
                            then
                              match args with
                              | (t,uu____4860)::[] ->
                                  let uu____4873 =
                                    let uu____4874 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____4874.FStar_Syntax_Syntax.n in
                                  (match uu____4873 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____4877::[],body,uu____4879) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____4905 -> tm)
                                   | uu____4907 -> tm)
                              | (uu____4908,Some
                                 (FStar_Syntax_Syntax.Implicit uu____4909))::
                                  (t,uu____4911)::[] ->
                                  let uu____4938 =
                                    let uu____4939 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____4939.FStar_Syntax_Syntax.n in
                                  (match uu____4938 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____4942::[],body,uu____4944) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____4970 -> tm)
                                   | uu____4972 -> tm)
                              | uu____4973 -> tm
                            else reduce_equality cfg tm)))))
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                FStar_Syntax_Syntax.tk = uu____4981;
                FStar_Syntax_Syntax.pos = uu____4982;
                FStar_Syntax_Syntax.vars = uu____4983;_},args)
             ->
             let uu____4999 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____4999
             then
               let uu____5000 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____5000 with
                | (Some (true ),uu____5033)::(uu____5034,(arg,uu____5036))::[]
                    -> arg
                | (uu____5077,(arg,uu____5079))::(Some (true ),uu____5080)::[]
                    -> arg
                | (Some (false ),uu____5121)::uu____5122::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____5160::(Some (false ),uu____5161)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____5199 -> tm)
             else
               (let uu____5209 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____5209
                then
                  let uu____5210 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____5210 with
                  | (Some (true ),uu____5243)::uu____5244::[] ->
                      w FStar_Syntax_Util.t_true
                  | uu____5282::(Some (true ),uu____5283)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),uu____5321)::(uu____5322,(arg,uu____5324))::[]
                      -> arg
                  | (uu____5365,(arg,uu____5367))::(Some (false ),uu____5368)::[]
                      -> arg
                  | uu____5409 -> tm
                else
                  (let uu____5419 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____5419
                   then
                     let uu____5420 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____5420 with
                     | uu____5453::(Some (true ),uu____5454)::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (false ),uu____5492)::uu____5493::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____5531)::(uu____5532,(arg,uu____5534))::[]
                         -> arg
                     | uu____5575 -> tm
                   else
                     (let uu____5585 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____5585
                      then
                        let uu____5586 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____5586 with
                        | (Some (true ),uu____5619)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____5643)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____5667 -> tm
                      else
                        (let uu____5677 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid in
                         if uu____5677
                         then
                           match args with
                           | (t,uu____5679)::[] ->
                               let uu____5692 =
                                 let uu____5693 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5693.FStar_Syntax_Syntax.n in
                               (match uu____5692 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5696::[],body,uu____5698) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5724 -> tm)
                                | uu____5726 -> tm)
                           | (uu____5727,Some (FStar_Syntax_Syntax.Implicit
                              uu____5728))::(t,uu____5730)::[] ->
                               let uu____5757 =
                                 let uu____5758 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5758.FStar_Syntax_Syntax.n in
                               (match uu____5757 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5761::[],body,uu____5763) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5789 -> tm)
                                | uu____5791 -> tm)
                           | uu____5792 -> tm
                         else
                           (let uu____5799 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid in
                            if uu____5799
                            then
                              match args with
                              | (t,uu____5801)::[] ->
                                  let uu____5814 =
                                    let uu____5815 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5815.FStar_Syntax_Syntax.n in
                                  (match uu____5814 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5818::[],body,uu____5820) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5846 -> tm)
                                   | uu____5848 -> tm)
                              | (uu____5849,Some
                                 (FStar_Syntax_Syntax.Implicit uu____5850))::
                                  (t,uu____5852)::[] ->
                                  let uu____5879 =
                                    let uu____5880 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5880.FStar_Syntax_Syntax.n in
                                  (match uu____5879 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5883::[],body,uu____5885) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5911 -> tm)
                                   | uu____5913 -> tm)
                              | uu____5914 -> tm
                            else reduce_equality cfg tm)))))
         | uu____5921 -> tm)
let is_norm_request hd1 args =
  let uu____5936 =
    let uu____5940 =
      let uu____5941 = FStar_Syntax_Util.un_uinst hd1 in
      uu____5941.FStar_Syntax_Syntax.n in
    (uu____5940, args) in
  match uu____5936 with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5946::uu____5947::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize_term
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5950::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize
  | uu____5952 -> false
let get_norm_request args =
  match args with
  | uu____5971::(tm,uu____5973)::[] -> tm
  | (tm,uu____5983)::[] -> tm
  | uu____5988 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___136_5995  ->
    match uu___136_5995 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.tk = uu____5997;
           FStar_Syntax_Syntax.pos = uu____5998;
           FStar_Syntax_Syntax.vars = uu____5999;_},uu____6000,uu____6001))::uu____6002
        -> true
    | uu____6008 -> false
let is_fstar_tactics_embed: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____6013 =
      let uu____6014 = FStar_Syntax_Util.un_uinst t in
      uu____6014.FStar_Syntax_Syntax.n in
    match uu____6013 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Syntax_Const.fstar_tactics_embed_lid
    | uu____6018 -> false
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
            (fun uu____6132  ->
               let uu____6133 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____6134 = FStar_Syntax_Print.term_to_string t1 in
               let uu____6135 =
                 let uu____6136 =
                   let uu____6138 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives.fst uu____6138 in
                 stack_to_string uu____6136 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____6133
                 uu____6134 uu____6135);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____6150 ->
               failwith "Impossible"
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (FStar_ST.write t1.FStar_Syntax_Syntax.tk None;
                rebuild cfg env stack1 t1)
           | FStar_Syntax_Syntax.Tm_uvar uu____6175 ->
               (FStar_ST.write t1.FStar_Syntax_Syntax.tk None;
                rebuild cfg env stack1 t1)
           | FStar_Syntax_Syntax.Tm_constant uu____6190 ->
               (FStar_ST.write t1.FStar_Syntax_Syntax.tk None;
                rebuild cfg env stack1 t1)
           | FStar_Syntax_Syntax.Tm_name uu____6195 ->
               (FStar_ST.write t1.FStar_Syntax_Syntax.tk None;
                rebuild cfg env stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6200;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____6201;_}
               ->
               (FStar_ST.write t1.FStar_Syntax_Syntax.tk None;
                rebuild cfg env stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6207;
                 FStar_Syntax_Syntax.fv_delta = uu____6208;
                 FStar_Syntax_Syntax.fv_qual = Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               ->
               (FStar_ST.write t1.FStar_Syntax_Syntax.tk None;
                rebuild cfg env stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6213;
                 FStar_Syntax_Syntax.fv_delta = uu____6214;
                 FStar_Syntax_Syntax.fv_qual = Some
                   (FStar_Syntax_Syntax.Record_ctor uu____6215);_}
               ->
               (FStar_ST.write t1.FStar_Syntax_Syntax.tk None;
                rebuild cfg env stack1 t1)
           | FStar_Syntax_Syntax.Tm_app
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.tk = uu____6224;
                  FStar_Syntax_Syntax.pos = uu____6225;
                  FStar_Syntax_Syntax.vars = uu____6226;_},uu____6227)
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Syntax_Const.fstar_tactics_embed_lid
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               is_fstar_tactics_embed hd1 ->
               let hd2 = closure_as_term cfg env hd1 in
               let args1 = closures_as_args_delayed cfg env args in
               let t2 =
                 let uu___162_6268 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.tk =
                     (uu___162_6268.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___162_6268.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___162_6268.FStar_Syntax_Syntax.vars)
                 } in
               (FStar_ST.write t2.FStar_Syntax_Syntax.tk None;
                (let t3 = reduce_primops cfg t2 in rebuild cfg env stack1 t3))
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____6299 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____6299) && (is_norm_request hd1 args))
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
                 let uu___163_6312 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___163_6312.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___163_6312.primitive_steps)
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
                  FStar_Syntax_Syntax.tk = uu____6317;
                  FStar_Syntax_Syntax.pos = uu____6318;
                  FStar_Syntax_Syntax.vars = uu____6319;_},a1::a2::rest)
               ->
               let uu____6353 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6353 with
                | (hd1,uu____6364) ->
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
                    (FStar_Const.Const_reflect uu____6419);
                  FStar_Syntax_Syntax.tk = uu____6420;
                  FStar_Syntax_Syntax.pos = uu____6421;
                  FStar_Syntax_Syntax.vars = uu____6422;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____6445 = FStar_List.tl stack1 in
               norm cfg env uu____6445 (fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.tk = uu____6448;
                  FStar_Syntax_Syntax.pos = uu____6449;
                  FStar_Syntax_Syntax.vars = uu____6450;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____6473 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6473 with
                | (reify_head,uu____6484) ->
                    let a1 =
                      let uu____6500 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (fst a) in
                      FStar_Syntax_Subst.compress uu____6500 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____6503);
                            FStar_Syntax_Syntax.tk = uu____6504;
                            FStar_Syntax_Syntax.pos = uu____6505;
                            FStar_Syntax_Syntax.vars = uu____6506;_},a2::[])
                         -> norm cfg env stack1 (fst a2)
                     | uu____6531 ->
                         let stack2 =
                           (App
                              (reify_head, None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____6539 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____6539
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____6546 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____6546
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____6549 =
                      let uu____6553 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____6553, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____6549 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___137_6562  ->
                         match uu___137_6562 with
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
                    let uu____6566 = FStar_Syntax_Syntax.range_of_fv f in
                    FStar_TypeChecker_Env.set_range cfg.tcenv uu____6566 in
                  let uu____6567 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  match uu____6567 with
                  | None  ->
                      (log cfg
                         (fun uu____6574  ->
                            FStar_Util.print "Tm_fvar case 2\n" []);
                       rebuild cfg env stack1 t1)
                  | Some (us,t2) ->
                      (log cfg
                         (fun uu____6580  ->
                            let uu____6581 =
                              FStar_Syntax_Print.term_to_string t0 in
                            let uu____6582 =
                              FStar_Syntax_Print.term_to_string t2 in
                            FStar_Util.print2 ">>> Unfolded %s to %s\n"
                              uu____6581 uu____6582);
                       (let t3 =
                          let uu____6584 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 (UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant)) in
                          if uu____6584
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
                          | (UnivArgs (us',uu____6592))::stack2 ->
                              let env1 =
                                FStar_All.pipe_right us'
                                  (FStar_List.fold_left
                                     (fun env1  -> fun u  -> (Univ u) :: env1)
                                     env) in
                              norm cfg env1 stack2 t3
                          | uu____6605 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack1 t3
                          | uu____6606 ->
                              let uu____6607 =
                                let uu____6608 =
                                  FStar_Syntax_Print.lid_to_string
                                    (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                FStar_Util.format1
                                  "Impossible: missing universe instantiation on %s"
                                  uu____6608 in
                              failwith uu____6607
                        else norm cfg env stack1 t3)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____6611 = lookup_bvar env x in
               (match uu____6611 with
                | Univ uu____6612 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____6627 = FStar_ST.read r in
                      (match uu____6627 with
                       | Some (env2,t') ->
                           (log cfg
                              (fun uu____6646  ->
                                 let uu____6647 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____6648 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____6647
                                   uu____6648);
                            (let uu____6649 =
                               let uu____6650 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____6650.FStar_Syntax_Syntax.n in
                             match uu____6649 with
                             | FStar_Syntax_Syntax.Tm_abs uu____6653 ->
                                 norm cfg env2 stack1 t'
                             | uu____6668 -> rebuild cfg env2 stack1 t'))
                       | None  -> norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____6701)::uu____6702 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____6707)::uu____6708 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____6714,uu____6715))::stack_rest ->
                    (match c with
                     | Univ uu____6718 -> norm cfg (c :: env) stack_rest t1
                     | uu____6719 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____6722::[] ->
                              (match lopt with
                               | None  when FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____6735  ->
                                         let uu____6736 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6736);
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
                                           (fun uu___138_6750  ->
                                              match uu___138_6750 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____6751 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____6753  ->
                                         let uu____6754 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6754);
                                    norm cfg (c :: env) stack_rest body)
                               | Some (FStar_Util.Inl lc) when
                                   FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                                   ->
                                   (log cfg
                                      (fun uu____6765  ->
                                         let uu____6766 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6766);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____6767 when
                                   FStar_All.pipe_right cfg.steps
                                     (FStar_List.contains Reify)
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____6774 ->
                                   let cfg1 =
                                     let uu___164_6782 = cfg in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___164_6782.tcenv);
                                       delta_level =
                                         (uu___164_6782.delta_level);
                                       primitive_steps =
                                         (uu___164_6782.primitive_steps)
                                     } in
                                   let uu____6783 =
                                     closure_as_term cfg1 env t1 in
                                   rebuild cfg1 env stack1 uu____6783)
                          | uu____6784::tl1 ->
                              (log cfg
                                 (fun uu____6794  ->
                                    let uu____6795 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____6795);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___165_6819 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___165_6819.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____6832  ->
                          let uu____6833 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____6833);
                     norm cfg env stack2 t1)
                | (Debug uu____6834)::uu____6835 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____6837 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____6837
                    else
                      (let uu____6839 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____6839 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____6868 =
                                   let uu____6874 =
                                     let uu____6875 =
                                       let uu____6876 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____6876 in
                                     FStar_All.pipe_right uu____6875
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____6874
                                     (fun _0_31  -> FStar_Util.Inl _0_31) in
                                 FStar_All.pipe_right uu____6868
                                   (fun _0_32  -> Some _0_32)
                             | uu____6901 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____6915  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____6920  ->
                                 let uu____6921 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____6921);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___166_6931 = cfg in
                               let uu____6932 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___166_6931.steps);
                                 tcenv = (uu___166_6931.tcenv);
                                 delta_level = (uu___166_6931.delta_level);
                                 primitive_steps = uu____6932
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____6942)::uu____6943 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____6947 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____6947
                    else
                      (let uu____6949 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____6949 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____6978 =
                                   let uu____6984 =
                                     let uu____6985 =
                                       let uu____6986 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____6986 in
                                     FStar_All.pipe_right uu____6985
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____6984
                                     (fun _0_33  -> FStar_Util.Inl _0_33) in
                                 FStar_All.pipe_right uu____6978
                                   (fun _0_34  -> Some _0_34)
                             | uu____7011 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7025  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7030  ->
                                 let uu____7031 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7031);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___166_7041 = cfg in
                               let uu____7042 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___166_7041.steps);
                                 tcenv = (uu___166_7041.tcenv);
                                 delta_level = (uu___166_7041.delta_level);
                                 primitive_steps = uu____7042
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
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7090 =
                                   let uu____7096 =
                                     let uu____7097 =
                                       let uu____7098 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7098 in
                                     FStar_All.pipe_right uu____7097
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7096
                                     (fun _0_35  -> FStar_Util.Inl _0_35) in
                                 FStar_All.pipe_right uu____7090
                                   (fun _0_36  -> Some _0_36)
                             | uu____7123 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7137  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7142  ->
                                 let uu____7143 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7143);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___166_7153 = cfg in
                               let uu____7154 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___166_7153.steps);
                                 tcenv = (uu___166_7153.tcenv);
                                 delta_level = (uu___166_7153.delta_level);
                                 primitive_steps = uu____7154
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____7164)::uu____7165 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7170 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7170
                    else
                      (let uu____7172 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7172 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7201 =
                                   let uu____7207 =
                                     let uu____7208 =
                                       let uu____7209 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7209 in
                                     FStar_All.pipe_right uu____7208
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7207
                                     (fun _0_37  -> FStar_Util.Inl _0_37) in
                                 FStar_All.pipe_right uu____7201
                                   (fun _0_38  -> Some _0_38)
                             | uu____7234 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7248  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7253  ->
                                 let uu____7254 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7254);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___166_7264 = cfg in
                               let uu____7265 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___166_7264.steps);
                                 tcenv = (uu___166_7264.tcenv);
                                 delta_level = (uu___166_7264.delta_level);
                                 primitive_steps = uu____7265
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____7275)::uu____7276 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7286 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7286
                    else
                      (let uu____7288 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7288 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7317 =
                                   let uu____7323 =
                                     let uu____7324 =
                                       let uu____7325 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7325 in
                                     FStar_All.pipe_right uu____7324
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7323
                                     (fun _0_39  -> FStar_Util.Inl _0_39) in
                                 FStar_All.pipe_right uu____7317
                                   (fun _0_40  -> Some _0_40)
                             | uu____7350 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7364  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7369  ->
                                 let uu____7370 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7370);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___166_7380 = cfg in
                               let uu____7381 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___166_7380.steps);
                                 tcenv = (uu___166_7380.tcenv);
                                 delta_level = (uu___166_7380.delta_level);
                                 primitive_steps = uu____7381
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7391 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7391
                    else
                      (let uu____7393 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7393 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7422 =
                                   let uu____7428 =
                                     let uu____7429 =
                                       let uu____7430 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7430 in
                                     FStar_All.pipe_right uu____7429
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7428
                                     (fun _0_41  -> FStar_Util.Inl _0_41) in
                                 FStar_All.pipe_right uu____7422
                                   (fun _0_42  -> Some _0_42)
                             | uu____7455 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7469  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7474  ->
                                 let uu____7475 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7475);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___166_7485 = cfg in
                               let uu____7486 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___166_7485.steps);
                                 tcenv = (uu___166_7485.tcenv);
                                 delta_level = (uu___166_7485.delta_level);
                                 primitive_steps = uu____7486
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
                      (fun uu____7518  ->
                         fun stack2  ->
                           match uu____7518 with
                           | (a,aq) ->
                               let uu____7526 =
                                 let uu____7527 =
                                   let uu____7531 =
                                     let uu____7532 =
                                       let uu____7542 =
                                         FStar_Util.mk_ref None in
                                       (env, a, uu____7542, false) in
                                     Clos uu____7532 in
                                   (uu____7531, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____7527 in
                               uu____7526 :: stack2) args) in
               (log cfg
                  (fun uu____7564  ->
                     let uu____7565 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____7565);
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
                             ((let uu___167_7586 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___167_7586.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___167_7586.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____7587 ->
                      let uu____7590 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7590)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____7593 = FStar_Syntax_Subst.open_term [(x, None)] f in
                  match uu____7593 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____7609 =
                          let uu____7610 =
                            let uu____7615 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___168_7616 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___168_7616.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___168_7616.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____7615) in
                          FStar_Syntax_Syntax.Tm_refine uu____7610 in
                        mk uu____7609 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____7629 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____7629
               else
                 (let uu____7631 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____7631 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____7637 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  -> fun uu____7643  -> Dummy :: env1)
                               env) in
                        norm_comp cfg uu____7637 c1 in
                      let t2 =
                        let uu____7650 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____7650 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____7693)::uu____7694 -> norm cfg env stack1 t11
                | (Arg uu____7699)::uu____7700 -> norm cfg env stack1 t11
                | (App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.tk = uu____7705;
                       FStar_Syntax_Syntax.pos = uu____7706;
                       FStar_Syntax_Syntax.vars = uu____7707;_},uu____7708,uu____7709))::uu____7710
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____7716)::uu____7717 ->
                    norm cfg env stack1 t11
                | uu____7722 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____7725  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____7738 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____7738
                        | FStar_Util.Inr c ->
                            let uu____7746 = norm_comp cfg env c in
                            FStar_Util.Inr uu____7746 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____7751 =
                        mk
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (t12, (tc1, tacopt1), l))
                          t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____7751)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____7799,{
                              FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                uu____7800;
                              FStar_Syntax_Syntax.lbunivs = uu____7801;
                              FStar_Syntax_Syntax.lbtyp = uu____7802;
                              FStar_Syntax_Syntax.lbeff = uu____7803;
                              FStar_Syntax_Syntax.lbdef = uu____7804;_}::uu____7805),uu____7806)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____7832 =
                 (let uu____7833 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____7833) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____7834 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____7834))) in
               if uu____7832
               then
                 let env1 =
                   let uu____7837 =
                     let uu____7838 =
                       let uu____7848 = FStar_Util.mk_ref None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____7848,
                         false) in
                     Clos uu____7838 in
                   uu____7837 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____7872 =
                    let uu____7875 =
                      let uu____7876 =
                        let uu____7877 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____7877
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____7876] in
                    FStar_Syntax_Subst.open_term uu____7875 body in
                  match uu____7872 with
                  | (bs,body1) ->
                      let lb1 =
                        let uu___169_7883 = lb in
                        let uu____7884 =
                          let uu____7887 =
                            let uu____7888 = FStar_List.hd bs in
                            FStar_All.pipe_right uu____7888
                              FStar_Pervasives.fst in
                          FStar_All.pipe_right uu____7887
                            (fun _0_43  -> FStar_Util.Inl _0_43) in
                        let uu____7897 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____7900 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = uu____7884;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___169_7883.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____7897;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___169_7883.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____7900
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____7910  -> Dummy :: env1)
                             env) in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____7926 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____7926
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____7939 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____7961  ->
                        match uu____7961 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____8000 =
                                let uu___170_8001 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___170_8001.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___170_8001.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____8000 in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos in
                            let memo = FStar_Util.mk_ref None in
                            let rec_env1 = (Clos (env, fix_f_i, memo, true))
                              :: rec_env in
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1")))) (snd lbs)
                   (env, [], (Prims.parse_int "0")) in
               (match uu____7939 with
                | (rec_env,memos,uu____8061) ->
                    let uu____8076 =
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
                             let uu____8118 =
                               let uu____8119 =
                                 let uu____8129 = FStar_Util.mk_ref None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____8129, false) in
                               Clos uu____8119 in
                             uu____8118 :: env1) (snd lbs) env in
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
                             FStar_Syntax_Syntax.tk = uu____8167;
                             FStar_Syntax_Syntax.pos = uu____8168;
                             FStar_Syntax_Syntax.vars = uu____8169;_},uu____8170,uu____8171))::uu____8172
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____8178 -> false in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____8185 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____8185
                        then
                          let uu___171_8186 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___171_8186.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps = (uu___171_8186.primitive_steps)
                          }
                        else
                          (let uu___172_8188 = cfg in
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___172_8188.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta];
                             primitive_steps =
                               (uu___172_8188.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____8190 =
                         let uu____8191 = FStar_Syntax_Subst.compress head1 in
                         uu____8191.FStar_Syntax_Syntax.n in
                       match uu____8190 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____8205 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8205 with
                            | (uu____8206,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____8210 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____8217 =
                                         let uu____8218 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____8218.FStar_Syntax_Syntax.n in
                                       match uu____8217 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____8223,uu____8224))
                                           ->
                                           let uu____8233 =
                                             let uu____8234 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____8234.FStar_Syntax_Syntax.n in
                                           (match uu____8233 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____8239,msrc,uu____8241))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____8250 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                Some uu____8250
                                            | uu____8251 -> None)
                                       | uu____8252 -> None in
                                     let uu____8253 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____8253 with
                                      | Some e ->
                                          let lb1 =
                                            let uu___173_8257 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___173_8257.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___173_8257.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___173_8257.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Syntax_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____8258 =
                                            FStar_List.tl stack1 in
                                          let uu____8259 =
                                            let uu____8260 =
                                              let uu____8263 =
                                                let uu____8264 =
                                                  let uu____8272 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____8272) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____8264 in
                                              FStar_Syntax_Syntax.mk
                                                uu____8263 in
                                            uu____8260 None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____8258 uu____8259
                                      | None  ->
                                          let uu____8289 =
                                            let uu____8290 = is_return body in
                                            match uu____8290 with
                                            | Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____8293;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____8294;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____8295;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____8300 -> false in
                                          if uu____8289
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
                                               let uu____8320 =
                                                 let uu____8323 =
                                                   let uu____8324 =
                                                     let uu____8339 =
                                                       let uu____8341 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____8341] in
                                                     (uu____8339, body1,
                                                       (Some
                                                          (FStar_Util.Inr
                                                             (m1, [])))) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____8324 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8323 in
                                               uu____8320 None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____8374 =
                                                 let uu____8375 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____8375.FStar_Syntax_Syntax.n in
                                               match uu____8374 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____8381::uu____8382::[])
                                                   ->
                                                   let uu____8388 =
                                                     let uu____8391 =
                                                       let uu____8392 =
                                                         let uu____8397 =
                                                           let uu____8399 =
                                                             let uu____8400 =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____8400 in
                                                           let uu____8401 =
                                                             let uu____8403 =
                                                               let uu____8404
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____8404 in
                                                             [uu____8403] in
                                                           uu____8399 ::
                                                             uu____8401 in
                                                         (bind1, uu____8397) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____8392 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8391 in
                                                   uu____8388 None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____8416 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____8422 =
                                                 let uu____8425 =
                                                   let uu____8426 =
                                                     let uu____8436 =
                                                       let uu____8438 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____8439 =
                                                         let uu____8441 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____8442 =
                                                           let uu____8444 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____8445 =
                                                             let uu____8447 =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____8448 =
                                                               let uu____8450
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____8451
                                                                 =
                                                                 let uu____8453
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____8453] in
                                                               uu____8450 ::
                                                                 uu____8451 in
                                                             uu____8447 ::
                                                               uu____8448 in
                                                           uu____8444 ::
                                                             uu____8445 in
                                                         uu____8441 ::
                                                           uu____8442 in
                                                       uu____8438 ::
                                                         uu____8439 in
                                                     (bind_inst, uu____8436) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____8426 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8425 in
                                               uu____8422 None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____8465 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____8465 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____8483 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8483 with
                            | (uu____8484,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____8507 =
                                        let uu____8508 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____8508.FStar_Syntax_Syntax.n in
                                      match uu____8507 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____8514) -> t4
                                      | uu____8519 -> head2 in
                                    let uu____8520 =
                                      let uu____8521 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____8521.FStar_Syntax_Syntax.n in
                                    match uu____8520 with
                                    | FStar_Syntax_Syntax.Tm_fvar x -> Some x
                                    | uu____8526 -> None in
                                  let uu____8527 = maybe_extract_fv head2 in
                                  match uu____8527 with
                                  | Some x when
                                      let uu____8533 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____8533
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____8537 =
                                          maybe_extract_fv head3 in
                                        match uu____8537 with
                                        | Some uu____8540 -> Some true
                                        | uu____8541 -> Some false in
                                      (head3, action_unfolded)
                                  | uu____8544 -> (head2, None) in
                                ((let is_arg_impure uu____8555 =
                                    match uu____8555 with
                                    | (e,q) ->
                                        let uu____8560 =
                                          let uu____8561 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____8561.FStar_Syntax_Syntax.n in
                                        (match uu____8560 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____8576 -> false) in
                                  let uu____8577 =
                                    let uu____8578 =
                                      let uu____8582 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____8582 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____8578 in
                                  if uu____8577
                                  then
                                    let uu____8585 =
                                      let uu____8586 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____8586 in
                                    failwith uu____8585
                                  else ());
                                 (let uu____8588 =
                                    maybe_unfold_action head_app in
                                  match uu____8588 with
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
                                      let uu____8623 = FStar_List.tl stack1 in
                                      norm cfg env uu____8623 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____8637 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____8637 in
                           let uu____8638 = FStar_List.tl stack1 in
                           norm cfg env uu____8638 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____8714  ->
                                     match uu____8714 with
                                     | (pat,wopt,tm) ->
                                         let uu____8748 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____8748))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____8772 = FStar_List.tl stack1 in
                           norm cfg env uu____8772 tm
                       | uu____8773 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.tk = uu____8782;
                             FStar_Syntax_Syntax.pos = uu____8783;
                             FStar_Syntax_Syntax.vars = uu____8784;_},uu____8785,uu____8786))::uu____8787
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____8793 -> false in
                    if should_reify
                    then
                      let uu____8794 = FStar_List.tl stack1 in
                      let uu____8795 =
                        let uu____8796 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____8796 in
                      norm cfg env uu____8794 uu____8795
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____8799 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____8799
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___174_8805 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___174_8805.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___174_8805.primitive_steps)
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
                | uu____8807 ->
                    (match stack1 with
                     | uu____8808::uu____8809 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____8813)
                              -> norm cfg env ((Meta (m, r)) :: stack1) head1
                          | FStar_Syntax_Syntax.Meta_pattern args ->
                              let args1 = norm_pattern_args cfg env args in
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_pattern args1),
                                      (t1.FStar_Syntax_Syntax.pos))) ::
                                stack1) head1
                          | uu____8828 -> norm cfg env stack1 head1)
                     | [] ->
                         let head2 = norm cfg env [] head1 in
                         let m1 =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               let uu____8838 =
                                 norm_pattern_args cfg env args in
                               FStar_Syntax_Syntax.Meta_pattern uu____8838
                           | uu____8845 -> m in
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
              let uu____8857 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____8857 with
              | (uu____8858,return_repr) ->
                  let return_inst =
                    let uu____8865 =
                      let uu____8866 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____8866.FStar_Syntax_Syntax.n in
                    match uu____8865 with
                    | FStar_Syntax_Syntax.Tm_uinst (return_tm,uu____8872::[])
                        ->
                        let uu____8878 =
                          let uu____8881 =
                            let uu____8882 =
                              let uu____8887 =
                                let uu____8889 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____8889] in
                              (return_tm, uu____8887) in
                            FStar_Syntax_Syntax.Tm_uinst uu____8882 in
                          FStar_Syntax_Syntax.mk uu____8881 in
                        uu____8878 None e.FStar_Syntax_Syntax.pos
                    | uu____8901 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____8904 =
                    let uu____8907 =
                      let uu____8908 =
                        let uu____8918 =
                          let uu____8920 = FStar_Syntax_Syntax.as_arg t in
                          let uu____8921 =
                            let uu____8923 = FStar_Syntax_Syntax.as_arg e in
                            [uu____8923] in
                          uu____8920 :: uu____8921 in
                        (return_inst, uu____8918) in
                      FStar_Syntax_Syntax.Tm_app uu____8908 in
                    FStar_Syntax_Syntax.mk uu____8907 in
                  uu____8904 None e.FStar_Syntax_Syntax.pos
            else
              (let uu____8936 = FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____8936 with
               | None  ->
                   let uu____8938 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____8938
               | Some
                   { FStar_TypeChecker_Env.msource = uu____8939;
                     FStar_TypeChecker_Env.mtarget = uu____8940;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____8941;
                         FStar_TypeChecker_Env.mlift_term = None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | Some
                   { FStar_TypeChecker_Env.msource = uu____8952;
                     FStar_TypeChecker_Env.mtarget = uu____8953;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____8954;
                         FStar_TypeChecker_Env.mlift_term = Some lift;_};_}
                   ->
                   let uu____8972 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____8972)
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
                (fun uu____9002  ->
                   match uu____9002 with
                   | (a,imp) ->
                       let uu____9009 = norm cfg env [] a in
                       (uu____9009, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___175_9024 = comp1 in
            let uu____9027 =
              let uu____9028 =
                let uu____9034 = norm cfg env [] t in
                let uu____9035 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____9034, uu____9035) in
              FStar_Syntax_Syntax.Total uu____9028 in
            {
              FStar_Syntax_Syntax.n = uu____9027;
              FStar_Syntax_Syntax.tk = (uu___175_9024.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___175_9024.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___175_9024.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___176_9050 = comp1 in
            let uu____9053 =
              let uu____9054 =
                let uu____9060 = norm cfg env [] t in
                let uu____9061 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____9060, uu____9061) in
              FStar_Syntax_Syntax.GTotal uu____9054 in
            {
              FStar_Syntax_Syntax.n = uu____9053;
              FStar_Syntax_Syntax.tk = (uu___176_9050.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___176_9050.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___176_9050.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____9092  ->
                      match uu____9092 with
                      | (a,i) ->
                          let uu____9099 = norm cfg env [] a in
                          (uu____9099, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___139_9104  ->
                      match uu___139_9104 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____9108 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____9108
                      | f -> f)) in
            let uu___177_9112 = comp1 in
            let uu____9115 =
              let uu____9116 =
                let uu___178_9117 = ct in
                let uu____9118 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____9119 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____9122 = norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____9118;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___178_9117.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____9119;
                  FStar_Syntax_Syntax.effect_args = uu____9122;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____9116 in
            {
              FStar_Syntax_Syntax.n = uu____9115;
              FStar_Syntax_Syntax.tk = (uu___177_9112.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___177_9112.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___177_9112.FStar_Syntax_Syntax.vars)
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
            (let uu___179_9139 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___179_9139.tcenv);
               delta_level = (uu___179_9139.delta_level);
               primitive_steps = (uu___179_9139.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____9144 = norm1 t in
          FStar_Syntax_Util.non_informative uu____9144 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____9147 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___180_9161 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.tk = (uu___180_9161.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___180_9161.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___180_9161.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____9171 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____9171
            then
              let ct1 =
                match downgrade_ghost_effect_name
                        ct.FStar_Syntax_Syntax.effect_name
                with
                | Some pure_eff ->
                    let uu___181_9176 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___181_9176.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___181_9176.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___181_9176.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___181_9176.FStar_Syntax_Syntax.flags)
                    }
                | None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___182_9178 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___182_9178.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Syntax_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___182_9178.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___182_9178.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___182_9178.FStar_Syntax_Syntax.flags)
                    } in
              let uu___183_9179 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.tk =
                  (uu___183_9179.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___183_9179.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___183_9179.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____9185 -> c
and norm_binder:
  cfg ->
    env ->
      FStar_Syntax_Syntax.binder ->
        (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  =
  fun cfg  ->
    fun env  ->
      fun uu____9188  ->
        match uu____9188 with
        | (x,imp) ->
            let uu____9191 =
              let uu___184_9192 = x in
              let uu____9193 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___184_9192.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___184_9192.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____9193
              } in
            (uu____9191, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____9199 =
          FStar_List.fold_left
            (fun uu____9206  ->
               fun b  ->
                 match uu____9206 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____9199 with | (nbs,uu____9223) -> FStar_List.rev nbs
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
            let uu____9240 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
            if uu____9240
            then
              let t = norm cfg env [] lc.FStar_Syntax_Syntax.res_typ in
              let uu____9245 = FStar_Syntax_Util.is_total_lcomp lc in
              (if uu____9245
               then
                 let uu____9249 =
                   let uu____9252 =
                     let uu____9253 =
                       let uu____9256 = FStar_Syntax_Syntax.mk_Total t in
                       FStar_Syntax_Util.comp_set_flags uu____9256 flags in
                     FStar_Syntax_Util.lcomp_of_comp uu____9253 in
                   FStar_Util.Inl uu____9252 in
                 Some uu____9249
               else
                 (let uu____9260 =
                    let uu____9263 =
                      let uu____9264 =
                        let uu____9267 = FStar_Syntax_Syntax.mk_GTotal t in
                        FStar_Syntax_Util.comp_set_flags uu____9267 flags in
                      FStar_Syntax_Util.lcomp_of_comp uu____9264 in
                    FStar_Util.Inl uu____9263 in
                  Some uu____9260))
            else
              Some
                (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags))
        | uu____9280 -> lopt
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
              ((let uu____9292 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____9292
                then
                  let uu____9293 = FStar_Syntax_Print.term_to_string tm in
                  let uu____9294 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2 "Normalized %s to %s\n" uu____9293
                    uu____9294
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___185_9305 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___185_9305.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____9325  ->
                    let uu____9326 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____9326);
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
              let uu____9363 =
                let uu___186_9364 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___186_9364.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___186_9364.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___186_9364.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____9363
          | (Arg (Univ uu____9369,uu____9370,uu____9371))::uu____9372 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____9374,uu____9375))::uu____9376 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____9388),aq,r))::stack2 ->
              (log cfg
                 (fun uu____9404  ->
                    let uu____9405 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____9405);
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
                 (let uu____9416 = FStar_ST.read m in
                  match uu____9416 with
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
                  | Some (uu____9442,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq) None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.extend_app head1 (t, aq) None r in
              let uu____9464 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____9464
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____9471  ->
                    let uu____9472 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____9472);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____9477 =
                  log cfg
                    (fun uu____9479  ->
                       let uu____9480 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____9481 =
                         let uu____9482 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____9489  ->
                                   match uu____9489 with
                                   | (p,uu____9495,uu____9496) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____9482
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____9480 uu____9481);
                  (let whnf = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___140_9506  ->
                               match uu___140_9506 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____9507 -> false)) in
                     let steps' =
                       let uu____9510 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____9510
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___187_9513 = cfg in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___187_9513.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___187_9513.primitive_steps)
                     } in
                   let norm_or_whnf env2 t1 =
                     if whnf
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____9543 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____9556 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____9585  ->
                                   fun uu____9586  ->
                                     match (uu____9585, uu____9586) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____9640 = norm_pat env3 p1 in
                                         (match uu____9640 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____9556 with
                          | (pats1,env3) ->
                              ((let uu___188_9693 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.p =
                                    (uu___188_9693.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___189_9704 = x in
                           let uu____9705 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___189_9704.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___189_9704.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9705
                           } in
                         ((let uu___190_9710 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.p =
                               (uu___190_9710.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___191_9714 = x in
                           let uu____9715 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___191_9714.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___191_9714.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9715
                           } in
                         ((let uu___192_9720 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.p =
                               (uu___192_9720.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___193_9729 = x in
                           let uu____9730 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___193_9729.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___193_9729.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9730
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___194_9736 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.p =
                               (uu___194_9736.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf -> branches
                     | uu____9739 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____9742 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____9742 with
                                 | (p,wopt,e) ->
                                     let uu____9758 = norm_pat env1 p in
                                     (match uu____9758 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | None  -> None
                                            | Some w ->
                                                let uu____9779 =
                                                  norm_or_whnf env2 w in
                                                Some uu____9779 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____9783 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____9783) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____9793) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____9798 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____9799;
                        FStar_Syntax_Syntax.fv_delta = uu____9800;
                        FStar_Syntax_Syntax.fv_qual = Some
                          (FStar_Syntax_Syntax.Data_ctor );_}
                      -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____9801;
                        FStar_Syntax_Syntax.fv_delta = uu____9802;
                        FStar_Syntax_Syntax.fv_qual = Some
                          (FStar_Syntax_Syntax.Record_ctor uu____9803);_}
                      -> true
                  | uu____9807 -> false in
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
                  let uu____9903 = FStar_Syntax_Util.head_and_args scrutinee2 in
                  match uu____9903 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var uu____9935 ->
                           FStar_Util.Inl [scrutinee2]
                       | FStar_Syntax_Syntax.Pat_wild uu____9937 ->
                           FStar_Util.Inl [scrutinee2]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____9939 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____9951 ->
                                let uu____9952 =
                                  let uu____9953 = is_cons head1 in
                                  Prims.op_Negation uu____9953 in
                                FStar_Util.Inr uu____9952)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____9965 =
                             let uu____9966 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____9966.FStar_Syntax_Syntax.n in
                           (match uu____9965 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____9973 ->
                                let uu____9974 =
                                  let uu____9975 = is_cons head1 in
                                  Prims.op_Negation uu____9975 in
                                FStar_Util.Inr uu____9974))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____10009)::rest_a,(p1,uu____10012)::rest_p) ->
                      let uu____10040 = matches_pat t1 p1 in
                      (match uu____10040 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____10054 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____10125 = matches_pat scrutinee1 p1 in
                      (match uu____10125 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____10135  ->
                                 let uu____10136 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____10137 =
                                   let uu____10138 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____10138
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____10136 uu____10137);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____10147 =
                                        let uu____10148 =
                                          let uu____10158 =
                                            FStar_Util.mk_ref (Some ([], t1)) in
                                          ([], t1, uu____10158, false) in
                                        Clos uu____10148 in
                                      uu____10147 :: env2) env1 s in
                             let uu____10181 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____10181))) in
                let uu____10182 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____10182
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___141_10196  ->
                match uu___141_10196 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | uu____10199 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____10203 -> d in
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
            let uu___195_10223 = config s e in
            {
              steps = (uu___195_10223.steps);
              tcenv = (uu___195_10223.tcenv);
              delta_level = (uu___195_10223.delta_level);
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
      fun t  -> let uu____10242 = config s e in norm_comp uu____10242 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____10249 = config [] env in norm_universe uu____10249 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun c  ->
      let uu____10256 = config [] env in ghost_to_pure_aux uu____10256 [] c
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
        let uu____10268 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____10268 in
      let uu____10269 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____10269
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | Some pure_eff ->
            let uu___196_10271 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___196_10271.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___196_10271.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____10272  ->
                    let uu____10273 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____10273))
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
            ((let uu____10286 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10286);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____10295 = config [AllowUnboundUniverses] env in
          norm_comp uu____10295 [] c
        with
        | e ->
            ((let uu____10299 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10299);
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
                   let uu____10336 =
                     let uu____10337 =
                       let uu____10342 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____10342) in
                     FStar_Syntax_Syntax.Tm_refine uu____10337 in
                   mk uu____10336 t01.FStar_Syntax_Syntax.pos
               | uu____10347 -> t2)
          | uu____10348 -> t2 in
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
        let uu____10370 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____10370 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____10386 ->
                 let uu____10390 = FStar_Syntax_Util.abs_formals e in
                 (match uu____10390 with
                  | (actuals,uu____10401,uu____10402) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____10424 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____10424 with
                         | (binders,args) ->
                             let uu____10434 =
                               FStar_Syntax_Syntax.mk_Tm_app e args None
                                 e.FStar_Syntax_Syntax.pos in
                             let uu____10437 =
                               let uu____10444 =
                                 FStar_All.pipe_right
                                   (FStar_Syntax_Util.lcomp_of_comp c)
                                   (fun _0_44  -> FStar_Util.Inl _0_44) in
                               FStar_All.pipe_right uu____10444
                                 (fun _0_45  -> Some _0_45) in
                             FStar_Syntax_Util.abs binders uu____10434
                               uu____10437)))
let eta_expand:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____10480 =
        let uu____10484 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
        (uu____10484, (t.FStar_Syntax_Syntax.n)) in
      match uu____10480 with
      | (Some sort,uu____10491) ->
          let uu____10493 = mk sort t.FStar_Syntax_Syntax.pos in
          eta_expand_with_type env t uu____10493
      | (uu____10494,FStar_Syntax_Syntax.Tm_name x) ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____10498 ->
          let uu____10502 = FStar_Syntax_Util.head_and_args t in
          (match uu____10502 with
           | (head1,args) ->
               let uu____10528 =
                 let uu____10529 = FStar_Syntax_Subst.compress head1 in
                 uu____10529.FStar_Syntax_Syntax.n in
               (match uu____10528 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____10532,thead) ->
                    let uu____10550 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____10550 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____10581 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___201_10585 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___201_10585.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___201_10585.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___201_10585.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___201_10585.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___201_10585.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___201_10585.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ = None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___201_10585.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___201_10585.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___201_10585.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___201_10585.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___201_10585.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___201_10585.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___201_10585.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___201_10585.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___201_10585.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___201_10585.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___201_10585.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___201_10585.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___201_10585.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___201_10585.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___201_10585.FStar_TypeChecker_Env.qname_and_index)
                                 }) t in
                            match uu____10581 with
                            | (uu____10586,ty,uu____10588) ->
                                eta_expand_with_type env t ty))
                | uu____10589 ->
                    let uu____10590 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___202_10594 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___202_10594.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___202_10594.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___202_10594.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___202_10594.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___202_10594.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___202_10594.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ = None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___202_10594.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___202_10594.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___202_10594.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___202_10594.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___202_10594.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___202_10594.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___202_10594.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___202_10594.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___202_10594.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___202_10594.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___202_10594.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___202_10594.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___202_10594.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___202_10594.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___202_10594.FStar_TypeChecker_Env.qname_and_index)
                         }) t in
                    (match uu____10590 with
                     | (uu____10595,ty,uu____10597) ->
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
            | (uu____10643,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c)) None
                  c.FStar_Syntax_Syntax.pos
            | (uu____10651,FStar_Util.Inl t) ->
                let uu____10655 =
                  let uu____10658 =
                    let uu____10659 =
                      let uu____10667 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____10667) in
                    FStar_Syntax_Syntax.Tm_arrow uu____10659 in
                  FStar_Syntax_Syntax.mk uu____10658 in
                uu____10655 None t.FStar_Syntax_Syntax.pos in
          let uu____10676 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____10676 with
          | (univ_names1,t1) ->
              let t2 = reduce_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____10693 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____10725 ->
                    let uu____10726 =
                      let uu____10731 =
                        let uu____10732 = FStar_Syntax_Subst.compress t3 in
                        uu____10732.FStar_Syntax_Syntax.n in
                      (uu____10731, tc) in
                    (match uu____10726 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____10748) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____10772) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____10798,FStar_Util.Inl uu____10799) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____10813 -> failwith "Impossible") in
              (match uu____10693 with
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
          let uu____10878 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____10878 with
          | (univ_names1,binders1,tc) ->
              let uu____10912 = FStar_Util.left tc in
              (univ_names1, binders1, uu____10912)
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
          let uu____10938 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____10938 with
          | (univ_names1,binders1,tc) ->
              let uu____10974 = FStar_Util.right tc in
              (univ_names1, binders1, uu____10974)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____11000 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____11000 with
           | (univ_names1,binders1,typ1) ->
               let uu___203_11016 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___203_11016.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___203_11016.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___203_11016.FStar_Syntax_Syntax.sigmeta)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___204_11028 = s in
          let uu____11029 =
            let uu____11030 =
              let uu____11035 = FStar_List.map (elim_uvars env) sigs in
              (uu____11035, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____11030 in
          {
            FStar_Syntax_Syntax.sigel = uu____11029;
            FStar_Syntax_Syntax.sigrng =
              (uu___204_11028.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___204_11028.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___204_11028.FStar_Syntax_Syntax.sigmeta)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____11047 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____11047 with
           | (univ_names1,uu____11057,typ1) ->
               let uu___205_11065 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___205_11065.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___205_11065.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___205_11065.FStar_Syntax_Syntax.sigmeta)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____11070 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____11070 with
           | (univ_names1,uu____11080,typ1) ->
               let uu___206_11088 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___206_11088.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___206_11088.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___206_11088.FStar_Syntax_Syntax.sigmeta)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids,attrs) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____11107 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____11107 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____11122 =
                            let uu____11123 =
                              FStar_Syntax_Subst.subst opening t in
                            reduce_uvar_solutions env uu____11123 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____11122 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___207_11126 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___207_11126.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___207_11126.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___208_11127 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids, attrs));
            FStar_Syntax_Syntax.sigrng =
              (uu___208_11127.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___208_11127.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___208_11127.FStar_Syntax_Syntax.sigmeta)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___209_11135 = s in
          let uu____11136 =
            let uu____11137 = reduce_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____11137 in
          {
            FStar_Syntax_Syntax.sigel = uu____11136;
            FStar_Syntax_Syntax.sigrng =
              (uu___209_11135.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___209_11135.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___209_11135.FStar_Syntax_Syntax.sigmeta)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____11141 = elim_uvars_aux_t env us [] t in
          (match uu____11141 with
           | (us1,uu____11151,t1) ->
               let uu___210_11159 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___210_11159.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___210_11159.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___210_11159.FStar_Syntax_Syntax.sigmeta)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11160 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____11162 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____11162 with
           | (univs1,binders,signature) ->
               let uu____11178 =
                 let uu____11183 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____11183 with
                 | (univs_opening,univs2) ->
                     let uu____11198 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____11198) in
               (match uu____11178 with
                | (univs_opening,univs_closing) ->
                    let uu____11208 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____11212 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____11213 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____11212, uu____11213) in
                    (match uu____11208 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____11230 =
                           match uu____11230 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____11242 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____11242 with
                                | (us1,t1) ->
                                    let uu____11249 =
                                      let uu____11252 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____11256 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____11252, uu____11256) in
                                    (match uu____11249 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____11264 =
                                           let uu____11267 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____11272 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____11267, uu____11272) in
                                         (match uu____11264 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____11282 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____11282 in
                                              let uu____11283 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____11283 with
                                               | (uu____11294,uu____11295,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____11304 =
                                                       let uu____11305 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____11305 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____11304 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____11310 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____11310 with
                           | (uu____11317,uu____11318,t1) -> t1 in
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
                             let uu____11372 =
                               let uu____11373 =
                                 FStar_Syntax_Subst.compress t in
                               uu____11373.FStar_Syntax_Syntax.n in
                             match uu____11372 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl typ,None ),None ) ->
                                 (defn, typ)
                             | uu____11421 -> failwith "Impossible" in
                           let uu____11428 =
                             elim_uvars_aux_t env
                               (FStar_List.append univs1
                                  a.FStar_Syntax_Syntax.action_univs)
                               (FStar_List.append binders
                                  a.FStar_Syntax_Syntax.action_params)
                               action_typ_templ in
                           match uu____11428 with
                           | (u_action_univs,b_action_params,res) ->
                               let action_univs =
                                 FStar_Util.nth_tail n1 u_action_univs in
                               let action_params =
                                 FStar_Util.nth_tail
                                   (FStar_List.length binders)
                                   b_action_params in
                               let uu____11460 =
                                 destruct_action_typ_templ res in
                               (match uu____11460 with
                                | (action_defn,action_typ) ->
                                    let uu___211_11477 = a in
                                    {
                                      FStar_Syntax_Syntax.action_name =
                                        (uu___211_11477.FStar_Syntax_Syntax.action_name);
                                      FStar_Syntax_Syntax.action_unqualified_name
                                        =
                                        (uu___211_11477.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___212_11479 = ed in
                           let uu____11480 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____11481 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____11482 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____11483 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____11484 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____11485 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____11486 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____11487 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____11488 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____11489 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____11490 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____11491 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____11492 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____11493 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___212_11479.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___212_11479.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____11480;
                             FStar_Syntax_Syntax.bind_wp = uu____11481;
                             FStar_Syntax_Syntax.if_then_else = uu____11482;
                             FStar_Syntax_Syntax.ite_wp = uu____11483;
                             FStar_Syntax_Syntax.stronger = uu____11484;
                             FStar_Syntax_Syntax.close_wp = uu____11485;
                             FStar_Syntax_Syntax.assert_p = uu____11486;
                             FStar_Syntax_Syntax.assume_p = uu____11487;
                             FStar_Syntax_Syntax.null_wp = uu____11488;
                             FStar_Syntax_Syntax.trivial = uu____11489;
                             FStar_Syntax_Syntax.repr = uu____11490;
                             FStar_Syntax_Syntax.return_repr = uu____11491;
                             FStar_Syntax_Syntax.bind_repr = uu____11492;
                             FStar_Syntax_Syntax.actions = uu____11493
                           } in
                         let uu___213_11495 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___213_11495.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___213_11495.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___213_11495.FStar_Syntax_Syntax.sigmeta)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___142_11506 =
            match uu___142_11506 with
            | None  -> None
            | Some (us,t) ->
                let uu____11521 = elim_uvars_aux_t env us [] t in
                (match uu____11521 with
                 | (us1,uu____11534,t1) -> Some (us1, t1)) in
          let sub_eff1 =
            let uu___214_11545 = sub_eff in
            let uu____11546 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____11548 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___214_11545.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___214_11545.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____11546;
              FStar_Syntax_Syntax.lift = uu____11548
            } in
          let uu___215_11550 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___215_11550.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___215_11550.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___215_11550.FStar_Syntax_Syntax.sigmeta)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____11558 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____11558 with
           | (univ_names1,binders1,comp1) ->
               let uu___216_11580 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___216_11580.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___216_11580.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___216_11580.FStar_Syntax_Syntax.sigmeta)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____11587 -> s