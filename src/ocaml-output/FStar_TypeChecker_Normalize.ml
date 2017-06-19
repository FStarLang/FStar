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
let uu___is_UnfoldTac: step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____68 -> false
let uu___is_PureSubtermsWithinComputations: step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____72 -> false
let uu___is_Simplify: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____76 -> false
let uu___is_EraseUniverses: step -> Prims.bool =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____80 -> false
let uu___is_AllowUnboundUniverses: step -> Prims.bool =
  fun projectee  ->
    match projectee with | AllowUnboundUniverses  -> true | uu____84 -> false
let uu___is_Reify: step -> Prims.bool =
  fun projectee  -> match projectee with | Reify  -> true | uu____88 -> false
let uu___is_CompressUvars: step -> Prims.bool =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____92 -> false
let uu___is_NoFullNorm: step -> Prims.bool =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____96 -> false
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
    match projectee with | Clos _0 -> true | uu____179 -> false
let __proj__Clos__item___0:
  closure ->
    (closure Prims.list* FStar_Syntax_Syntax.term* (closure Prims.list*
      FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo* Prims.bool)
  = fun projectee  -> match projectee with | Clos _0 -> _0
let uu___is_Univ: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____218 -> false
let __proj__Univ__item___0: closure -> FStar_Syntax_Syntax.universe =
  fun projectee  -> match projectee with | Univ _0 -> _0
let uu___is_Dummy: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____229 -> false
type env = closure Prims.list
let closure_to_string: closure -> Prims.string =
  fun uu___137_233  ->
    match uu___137_233 with
    | Clos (uu____234,t,uu____236,uu____237) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____248 -> "Univ"
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
    match projectee with | Arg _0 -> true | uu____373 -> false
let __proj__Arg__item___0:
  stack_elt -> (closure* FStar_Syntax_Syntax.aqual* FStar_Range.range) =
  fun projectee  -> match projectee with | Arg _0 -> _0
let uu___is_UnivArgs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____397 -> false
let __proj__UnivArgs__item___0:
  stack_elt -> (FStar_Syntax_Syntax.universe Prims.list* FStar_Range.range) =
  fun projectee  -> match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____421 -> false
let __proj__MemoLazy__item___0:
  stack_elt -> (env* FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo =
  fun projectee  -> match projectee with | MemoLazy _0 -> _0
let uu___is_Match: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____448 -> false
let __proj__Match__item___0: stack_elt -> (env* branches* FStar_Range.range)
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Abs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____475 -> false
let __proj__Abs__item___0:
  stack_elt ->
    (env* FStar_Syntax_Syntax.binders* env* FStar_Syntax_Syntax.residual_comp
      option* FStar_Range.range)
  = fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____508 -> false
let __proj__App__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.aqual* FStar_Range.range)
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Meta: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____531 -> false
let __proj__Meta__item___0:
  stack_elt -> (FStar_Syntax_Syntax.metadata* FStar_Range.range) =
  fun projectee  -> match projectee with | Meta _0 -> _0
let uu___is_Let: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____553 -> false
let __proj__Let__item___0:
  stack_elt ->
    (env* FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.letbinding*
      FStar_Range.range)
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Steps: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Steps _0 -> true | uu____582 -> false
let __proj__Steps__item___0:
  stack_elt ->
    (steps* primitive_step Prims.list* FStar_TypeChecker_Env.delta_level
      Prims.list)
  = fun projectee  -> match projectee with | Steps _0 -> _0
let uu___is_Debug: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____609 -> false
let __proj__Debug__item___0: stack_elt -> FStar_Syntax_Syntax.term =
  fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list
let mk t r = FStar_Syntax_Syntax.mk t None r
let set_memo r t =
  let uu____657 = FStar_ST.read r in
  match uu____657 with
  | Some uu____662 -> failwith "Unexpected set_memo: thunk already evaluated"
  | None  -> FStar_ST.write r (Some t)
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____671 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____671 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___138_676  ->
    match uu___138_676 with
    | Arg (c,uu____678,uu____679) ->
        let uu____680 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____680
    | MemoLazy uu____681 -> "MemoLazy"
    | Abs (uu____685,bs,uu____687,uu____688,uu____689) ->
        let uu____692 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____692
    | UnivArgs uu____697 -> "UnivArgs"
    | Match uu____701 -> "Match"
    | App (t,uu____706,uu____707) ->
        let uu____708 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____708
    | Meta (m,uu____710) -> "Meta"
    | Let uu____711 -> "Let"
    | Steps (uu____716,uu____717,uu____718) -> "Steps"
    | Debug t ->
        let uu____724 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____724
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____730 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____730 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____744 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____744 then f () else ()
let is_empty uu___139_753 =
  match uu___139_753 with | [] -> true | uu____755 -> false
let lookup_bvar env x =
  try FStar_List.nth env x.FStar_Syntax_Syntax.index
  with
  | uu____773 ->
      let uu____774 =
        let uu____775 = FStar_Syntax_Print.db_to_string x in
        FStar_Util.format1 "Failed to find %s\n" uu____775 in
      failwith uu____774
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
          let uu____806 =
            FStar_List.fold_left
              (fun uu____815  ->
                 fun u1  ->
                   match uu____815 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____830 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____830 with
                        | (k_u,n1) ->
                            let uu____839 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____839
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____806 with
          | (uu____849,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____865 = FStar_List.nth env x in
                 match uu____865 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____868 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____872 ->
                   let uu____873 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____873
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____877 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____880 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____885 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____885 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____896 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____896 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____901 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____904 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____904 with
                                  | (uu____907,m) -> n1 <= m)) in
                        if uu____901 then rest1 else us1
                    | uu____911 -> us1)
               | uu____914 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____917 = aux u3 in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____917 in
        let uu____919 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____919
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____921 = aux u in
           match uu____921 with
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
          (fun uu____1009  ->
             let uu____1010 = FStar_Syntax_Print.tag_of_term t in
             let uu____1011 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1010
               uu____1011);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1012 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1015 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____1030 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____1031 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____1032 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____1033 -> t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____1043 =
                    let uu____1044 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____1044 in
                  mk uu____1043 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____1051 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____1051
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____1053 = lookup_bvar env x in
                  (match uu____1053 with
                   | Univ uu____1054 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____1058) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____1116 = closures_as_binders_delayed cfg env bs in
                  (match uu____1116 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____1136 =
                         let uu____1137 =
                           let uu____1147 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____1147) in
                         FStar_Syntax_Syntax.Tm_abs uu____1137 in
                       mk uu____1136 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____1167 = closures_as_binders_delayed cfg env bs in
                  (match uu____1167 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____1198 =
                    let uu____1205 =
                      let uu____1209 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____1209] in
                    closures_as_binders_delayed cfg env uu____1205 in
                  (match uu____1198 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____1223 =
                         let uu____1224 =
                           let uu____1229 =
                             let uu____1230 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____1230
                               FStar_Pervasives.fst in
                           (uu____1229, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____1224 in
                       mk uu____1223 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____1298 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____1298
                    | FStar_Util.Inr c ->
                        let uu____1312 = close_comp cfg env c in
                        FStar_Util.Inr uu____1312 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____1327 =
                    let uu____1328 =
                      let uu____1346 = closure_as_term_delayed cfg env t11 in
                      (uu____1346, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____1328 in
                  mk uu____1327 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____1384 =
                    let uu____1385 =
                      let uu____1390 = closure_as_term_delayed cfg env t' in
                      let uu____1393 =
                        let uu____1394 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____1394 in
                      (uu____1390, uu____1393) in
                    FStar_Syntax_Syntax.Tm_meta uu____1385 in
                  mk uu____1384 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____1436 =
                    let uu____1437 =
                      let uu____1442 = closure_as_term_delayed cfg env t' in
                      let uu____1445 =
                        let uu____1446 =
                          let uu____1451 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____1451) in
                        FStar_Syntax_Syntax.Meta_monadic uu____1446 in
                      (uu____1442, uu____1445) in
                    FStar_Syntax_Syntax.Tm_meta uu____1437 in
                  mk uu____1436 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____1470 =
                    let uu____1471 =
                      let uu____1476 = closure_as_term_delayed cfg env t' in
                      let uu____1479 =
                        let uu____1480 =
                          let uu____1486 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____1486) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____1480 in
                      (uu____1476, uu____1479) in
                    FStar_Syntax_Syntax.Tm_meta uu____1471 in
                  mk uu____1470 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____1499 =
                    let uu____1500 =
                      let uu____1505 = closure_as_term_delayed cfg env t' in
                      (uu____1505, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____1500 in
                  mk uu____1499 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____1526  -> Dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let body1 =
                    match lb.FStar_Syntax_Syntax.lbname with
                    | FStar_Util.Inr uu____1537 -> body
                    | FStar_Util.Inl uu____1538 ->
                        closure_as_term cfg (Dummy :: env0) body in
                  let lb1 =
                    let uu___153_1540 = lb in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___153_1540.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___153_1540.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = typ;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___153_1540.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = def
                    } in
                  mk (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((uu____1547,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____1571  -> fun env2  -> Dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____1576 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____1576
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____1580  -> fun env2  -> Dummy :: env2) lbs
                          env_univs in
                    let uu___154_1583 = lb in
                    let uu____1584 =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let uu____1587 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___154_1583.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___154_1583.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = uu____1584;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___154_1583.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____1587
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____1598  -> fun env1  -> Dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____1653 =
                    match uu____1653 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____1699 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____1715 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____1749  ->
                                        fun uu____1750  ->
                                          match (uu____1749, uu____1750) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____1815 =
                                                norm_pat env3 p1 in
                                              (match uu____1815 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____1715 with
                               | (pats1,env3) ->
                                   ((let uu___155_1881 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.ty =
                                         (uu___155_1881.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___155_1881.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___156_1895 = x in
                                let uu____1896 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___156_1895.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___156_1895.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1896
                                } in
                              ((let uu___157_1902 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___157_1902.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___157_1902.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___158_1907 = x in
                                let uu____1908 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___158_1907.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___158_1907.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1908
                                } in
                              ((let uu___159_1914 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___159_1914.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___159_1914.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___160_1924 = x in
                                let uu____1925 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___160_1924.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___160_1924.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1925
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___161_1932 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___161_1932.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___161_1932.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____1935 = norm_pat env1 pat in
                        (match uu____1935 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | None  -> None
                               | Some w ->
                                   let uu____1959 =
                                     closure_as_term cfg env2 w in
                                   Some uu____1959 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____1964 =
                    let uu____1965 =
                      let uu____1981 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____1981) in
                    FStar_Syntax_Syntax.Tm_match uu____1965 in
                  mk uu____1964 t1.FStar_Syntax_Syntax.pos))
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
        | uu____2034 -> closure_as_term cfg env t
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
        | uu____2050 ->
            FStar_List.map
              (fun uu____2060  ->
                 match uu____2060 with
                 | (x,imp) ->
                     let uu____2075 = closure_as_term_delayed cfg env x in
                     (uu____2075, imp)) args
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
        let uu____2087 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____2111  ->
                  fun uu____2112  ->
                    match (uu____2111, uu____2112) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___162_2156 = b in
                          let uu____2157 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___162_2156.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___162_2156.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____2157
                          } in
                        let env2 = Dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____2087 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____2204 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____2216 = closure_as_term_delayed cfg env t in
                 let uu____2217 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____2216 uu____2217
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____2227 = closure_as_term_delayed cfg env t in
                 let uu____2228 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____2227 uu____2228
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
                        (fun uu___140_2244  ->
                           match uu___140_2244 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____2248 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____2248
                           | f -> f)) in
                 let uu____2252 =
                   let uu___163_2253 = c1 in
                   let uu____2254 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____2254;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___163_2253.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____2252)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags  ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___141_2259  ->
            match uu___141_2259 with
            | FStar_Syntax_Syntax.DECREASES uu____2260 -> false
            | uu____2263 -> true))
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
                   (fun uu___142_2275  ->
                      match uu___142_2275 with
                      | FStar_Syntax_Syntax.DECREASES uu____2276 -> false
                      | uu____2279 -> true)) in
            let rc1 =
              let uu___164_2281 = rc in
              let uu____2282 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___164_2281.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____2282;
                FStar_Syntax_Syntax.residual_flags = flags
              } in
            Some rc1
        | uu____2288 -> lopt
let built_in_primitive_steps: primitive_step Prims.list =
  let const_as_tm c p = mk (FStar_Syntax_Syntax.Tm_constant c) p in
  let int_as_const p i =
    let uu____2307 =
      let uu____2308 =
        let uu____2314 = FStar_Util.string_of_int i in (uu____2314, None) in
      FStar_Const.Const_int uu____2308 in
    const_as_tm uu____2307 p in
  let bool_as_const p b = const_as_tm (FStar_Const.Const_bool b) p in
  let string_as_const p b =
    const_as_tm
      (FStar_Const.Const_string ((FStar_Util.bytes_of_string b), p)) p in
  let arg_as_int uu____2341 =
    match uu____2341 with
    | (a,uu____2346) ->
        let uu____2348 =
          let uu____2349 = FStar_Syntax_Subst.compress a in
          uu____2349.FStar_Syntax_Syntax.n in
        (match uu____2348 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i,None ))
             ->
             let uu____2359 = FStar_Util.int_of_string i in Some uu____2359
         | uu____2360 -> None) in
  let arg_as_bounded_int uu____2369 =
    match uu____2369 with
    | (a,uu____2376) ->
        let uu____2380 =
          let uu____2381 = FStar_Syntax_Subst.compress a in
          uu____2381.FStar_Syntax_Syntax.n in
        (match uu____2380 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.tk = uu____2388;
                FStar_Syntax_Syntax.pos = uu____2389;
                FStar_Syntax_Syntax.vars = uu____2390;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,None ));
                                                            FStar_Syntax_Syntax.tk
                                                              = uu____2392;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____2393;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____2394;_},uu____2395)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____2426 =
               let uu____2429 = FStar_Util.int_of_string i in
               (fv1, uu____2429) in
             Some uu____2426
         | uu____2432 -> None) in
  let arg_as_bool uu____2441 =
    match uu____2441 with
    | (a,uu____2446) ->
        let uu____2448 =
          let uu____2449 = FStar_Syntax_Subst.compress a in
          uu____2449.FStar_Syntax_Syntax.n in
        (match uu____2448 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
             Some b
         | uu____2454 -> None) in
  let arg_as_char uu____2461 =
    match uu____2461 with
    | (a,uu____2466) ->
        let uu____2468 =
          let uu____2469 = FStar_Syntax_Subst.compress a in
          uu____2469.FStar_Syntax_Syntax.n in
        (match uu____2468 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
             Some c
         | uu____2474 -> None) in
  let arg_as_string uu____2481 =
    match uu____2481 with
    | (a,uu____2486) ->
        let uu____2488 =
          let uu____2489 = FStar_Syntax_Subst.compress a in
          uu____2489.FStar_Syntax_Syntax.n in
        (match uu____2488 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (bytes,uu____2494)) -> Some (FStar_Util.string_of_bytes bytes)
         | uu____2497 -> None) in
  let arg_as_list f uu____2518 =
    match uu____2518 with
    | (a,uu____2527) ->
        let rec sequence l =
          match l with
          | [] -> Some []
          | (None )::uu____2546 -> None
          | (Some x)::xs ->
              let uu____2556 = sequence xs in
              (match uu____2556 with
               | None  -> None
               | Some xs' -> Some (x :: xs')) in
        let uu____2567 = FStar_Syntax_Util.list_elements a in
        (match uu____2567 with
         | None  -> None
         | Some elts ->
             let uu____2577 =
               FStar_List.map
                 (fun x  ->
                    let uu____2582 = FStar_Syntax_Syntax.as_arg x in
                    f uu____2582) elts in
             sequence uu____2577) in
  let lift_unary f aopts =
    match aopts with
    | (Some a)::[] -> let uu____2612 = f a in Some uu____2612
    | uu____2613 -> None in
  let lift_binary f aopts =
    match aopts with
    | (Some a0)::(Some a1)::[] -> let uu____2652 = f a0 a1 in Some uu____2652
    | uu____2653 -> None in
  let unary_op as_a f r args =
    let uu____2697 = FStar_List.map as_a args in lift_unary (f r) uu____2697 in
  let binary_op as_a f r args =
    let uu____2747 = FStar_List.map as_a args in lift_binary (f r) uu____2747 in
  let as_primitive_step uu____2764 =
    match uu____2764 with
    | (l,arity,f) ->
        { name = l; arity; strong_reduction_ok = true; interpretation = f } in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  -> fun x  -> let uu____2802 = f x in int_as_const r uu____2802) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2825 = f x y in int_as_const r uu____2825) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  -> fun x  -> let uu____2842 = f x in bool_as_const r uu____2842) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2865 = f x y in bool_as_const r uu____2865) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2888 = f x y in string_as_const r uu____2888) in
  let list_of_string' rng s =
    let name l =
      let uu____2902 =
        let uu____2903 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            None in
        FStar_Syntax_Syntax.Tm_fvar uu____2903 in
      mk uu____2902 rng in
    let char_t = name FStar_Syntax_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____2913 =
      let uu____2915 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____2915 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____2913 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Const.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in int_as_const rng r in
  let string_concat' rng args =
    match args with
    | a1::a2::[] ->
        let uu____2969 = arg_as_string a1 in
        (match uu____2969 with
         | Some s1 ->
             let uu____2973 = arg_as_list arg_as_string a2 in
             (match uu____2973 with
              | Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____2981 = string_as_const rng r in Some uu____2981
              | uu____2982 -> None)
         | uu____2985 -> None)
    | uu____2987 -> None in
  let string_of_int1 rng i =
    let uu____2998 = FStar_Util.string_of_int i in
    string_as_const rng uu____2998 in
  let string_of_bool1 rng b =
    string_as_const rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____3014 = FStar_Util.string_of_int i in
    string_as_const rng uu____3014 in
  let string_of_bool2 rng b =
    string_as_const rng (if b then "true" else "false") in
  let basic_ops =
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
                                    let uu____3193 =
                                      let uu____3203 =
                                        let uu____3212 =
                                          FStar_Syntax_Const.p2l
                                            ["FStar";
                                            "String";
                                            "list_of_string"] in
                                        (uu____3212, (Prims.parse_int "1"),
                                          (unary_op arg_as_string
                                             list_of_string')) in
                                      let uu____3218 =
                                        let uu____3228 =
                                          let uu____3237 =
                                            FStar_Syntax_Const.p2l
                                              ["FStar";
                                              "String";
                                              "string_of_list"] in
                                          (uu____3237, (Prims.parse_int "1"),
                                            (unary_op
                                               (arg_as_list arg_as_char)
                                               string_of_list')) in
                                        let uu____3244 =
                                          let uu____3254 =
                                            let uu____3266 =
                                              FStar_Syntax_Const.p2l
                                                ["FStar"; "String"; "concat"] in
                                            (uu____3266,
                                              (Prims.parse_int "2"),
                                              string_concat') in
                                          [uu____3254] in
                                        uu____3228 :: uu____3244 in
                                      uu____3203 :: uu____3218 in
                                    (FStar_Syntax_Const.string_compare,
                                      (Prims.parse_int "2"),
                                      (binary_op arg_as_string
                                         string_compare'))
                                      :: uu____3193 in
                                  (FStar_Syntax_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_bool string_of_bool2))
                                    :: uu____3183 in
                                (FStar_Syntax_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (unary_op arg_as_int string_of_int2)) ::
                                  uu____3173 in
                              (FStar_Syntax_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____3163 in
                            (FStar_Syntax_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____3153 in
                          (FStar_Syntax_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____3143 in
                        (FStar_Syntax_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____3133 in
                      (FStar_Syntax_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____3123 in
                    (FStar_Syntax_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
                      :: uu____3113 in
                  (FStar_Syntax_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____3103 in
                (FStar_Syntax_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____3093 in
              (FStar_Syntax_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____3083 in
            (FStar_Syntax_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____3073 in
          (FStar_Syntax_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____3063 in
        (FStar_Syntax_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____3053 in
      (FStar_Syntax_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____3043 in
    (FStar_Syntax_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____3033 in
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
      let uu____3590 =
        let uu____3591 =
          let uu____3592 = FStar_Syntax_Syntax.as_arg c in [uu____3592] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____3591 in
      uu____3590 None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____3616 =
              let uu____3625 = FStar_Syntax_Const.p2l ["FStar"; m; "add"] in
              (uu____3625, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____3634  ->
                        fun uu____3635  ->
                          match (uu____3634, uu____3635) with
                          | ((int_to_t1,x),(uu____3646,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____3652 =
              let uu____3662 =
                let uu____3671 = FStar_Syntax_Const.p2l ["FStar"; m; "sub"] in
                (uu____3671, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____3680  ->
                          fun uu____3681  ->
                            match (uu____3680, uu____3681) with
                            | ((int_to_t1,x),(uu____3692,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____3698 =
                let uu____3708 =
                  let uu____3717 = FStar_Syntax_Const.p2l ["FStar"; m; "mul"] in
                  (uu____3717, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____3726  ->
                            fun uu____3727  ->
                              match (uu____3726, uu____3727) with
                              | ((int_to_t1,x),(uu____3738,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____3708] in
              uu____3662 :: uu____3698 in
            uu____3616 :: uu____3652)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_bool neg rng args =
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) rng in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) rng in
    match args with
    | (_typ,uu____3813)::(a1,uu____3815)::(a2,uu____3817)::[] ->
        let uu____3846 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3846 with
         | FStar_Syntax_Util.Equal  -> Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  -> Some (if neg then tru else fal)
         | uu____3858 -> None)
    | uu____3859 -> failwith "Unexpected number of arguments" in
  let interp_prop r args =
    match args with
    | (_typ,uu____3872)::(a1,uu____3874)::(a2,uu____3876)::[] ->
        let uu____3905 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3905 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___165_3909 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___165_3909.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___165_3909.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___165_3909.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___166_3916 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___166_3916.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___166_3916.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___166_3916.FStar_Syntax_Syntax.vars)
                })
         | uu____3921 -> None)
    | (_typ,uu____3923)::uu____3924::(a1,uu____3926)::(a2,uu____3928)::[] ->
        let uu____3965 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3965 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___165_3969 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___165_3969.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___165_3969.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___165_3969.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___166_3976 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___166_3976.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___166_3976.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___166_3976.FStar_Syntax_Syntax.vars)
                })
         | uu____3981 -> None)
    | uu____3982 -> failwith "Unexpected number of arguments" in
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
      let uu____3994 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops cfg.steps) in
      if uu____3994
      then tm
      else
        (let uu____3996 = FStar_Syntax_Util.head_and_args tm in
         match uu____3996 with
         | (head1,args) ->
             let uu____4022 =
               let uu____4023 = FStar_Syntax_Util.un_uinst head1 in
               uu____4023.FStar_Syntax_Syntax.n in
             (match uu____4022 with
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____4027 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps in
                  (match uu____4027 with
                   | None  -> tm
                   | Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then tm
                       else
                         (let uu____4039 =
                            prim_step.interpretation
                              head1.FStar_Syntax_Syntax.pos args in
                          match uu____4039 with
                          | None  -> tm
                          | Some reduced -> reduced))
              | uu____4042 -> tm))
let reduce_equality:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___167_4049 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___167_4049.tcenv);
           delta_level = (uu___167_4049.delta_level);
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
        let uu___168_4071 = t in
        {
          FStar_Syntax_Syntax.n = (uu___168_4071.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___168_4071.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___168_4071.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid ->
            Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid ->
            Some false
        | uu____4090 -> None in
      let simplify arg = ((simp_t (fst arg)), arg) in
      let tm1 = reduce_primops cfg tm in
      let uu____4118 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps) in
      if uu____4118
      then tm1
      else
        (match tm1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.tk = uu____4121;
                     FStar_Syntax_Syntax.pos = uu____4122;
                     FStar_Syntax_Syntax.vars = uu____4123;_},uu____4124);
                FStar_Syntax_Syntax.tk = uu____4125;
                FStar_Syntax_Syntax.pos = uu____4126;
                FStar_Syntax_Syntax.vars = uu____4127;_},args)
             ->
             let uu____4147 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____4147
             then
               let uu____4148 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____4148 with
                | (Some (true ),uu____4181)::(uu____4182,(arg,uu____4184))::[]
                    -> arg
                | (uu____4225,(arg,uu____4227))::(Some (true ),uu____4228)::[]
                    -> arg
                | (Some (false ),uu____4269)::uu____4270::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4308::(Some (false ),uu____4309)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4347 -> tm1)
             else
               (let uu____4357 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____4357
                then
                  let uu____4358 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____4358 with
                  | (Some (true ),uu____4391)::uu____4392::[] ->
                      w FStar_Syntax_Util.t_true
                  | uu____4430::(Some (true ),uu____4431)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),uu____4469)::(uu____4470,(arg,uu____4472))::[]
                      -> arg
                  | (uu____4513,(arg,uu____4515))::(Some (false ),uu____4516)::[]
                      -> arg
                  | uu____4557 -> tm1
                else
                  (let uu____4567 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____4567
                   then
                     let uu____4568 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____4568 with
                     | uu____4601::(Some (true ),uu____4602)::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (false ),uu____4640)::uu____4641::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____4679)::(uu____4680,(arg,uu____4682))::[]
                         -> arg
                     | (uu____4723,(p,uu____4725))::(uu____4726,(q,uu____4728))::[]
                         ->
                         let uu____4770 = FStar_Syntax_Util.term_eq p q in
                         (if uu____4770
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____4772 -> tm1
                   else
                     (let uu____4782 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____4782
                      then
                        let uu____4783 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____4783 with
                        | (Some (true ),uu____4816)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____4840)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____4864 -> tm1
                      else
                        (let uu____4874 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid in
                         if uu____4874
                         then
                           match args with
                           | (t,uu____4876)::[] ->
                               let uu____4889 =
                                 let uu____4890 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____4890.FStar_Syntax_Syntax.n in
                               (match uu____4889 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____4893::[],body,uu____4895) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____4911 -> tm1)
                                | uu____4913 -> tm1)
                           | (uu____4914,Some (FStar_Syntax_Syntax.Implicit
                              uu____4915))::(t,uu____4917)::[] ->
                               let uu____4944 =
                                 let uu____4945 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____4945.FStar_Syntax_Syntax.n in
                               (match uu____4944 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____4948::[],body,uu____4950) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____4966 -> tm1)
                                | uu____4968 -> tm1)
                           | uu____4969 -> tm1
                         else
                           (let uu____4976 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid in
                            if uu____4976
                            then
                              match args with
                              | (t,uu____4978)::[] ->
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
                                        | uu____5013 -> tm1)
                                   | uu____5015 -> tm1)
                              | (uu____5016,Some
                                 (FStar_Syntax_Syntax.Implicit uu____5017))::
                                  (t,uu____5019)::[] ->
                                  let uu____5046 =
                                    let uu____5047 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5047.FStar_Syntax_Syntax.n in
                                  (match uu____5046 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5050::[],body,uu____5052) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5068 -> tm1)
                                   | uu____5070 -> tm1)
                              | uu____5071 -> tm1
                            else reduce_equality cfg tm1)))))
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                FStar_Syntax_Syntax.tk = uu____5079;
                FStar_Syntax_Syntax.pos = uu____5080;
                FStar_Syntax_Syntax.vars = uu____5081;_},args)
             ->
             let uu____5097 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____5097
             then
               let uu____5098 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____5098 with
                | (Some (true ),uu____5131)::(uu____5132,(arg,uu____5134))::[]
                    -> arg
                | (uu____5175,(arg,uu____5177))::(Some (true ),uu____5178)::[]
                    -> arg
                | (Some (false ),uu____5219)::uu____5220::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____5258::(Some (false ),uu____5259)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____5297 -> tm1)
             else
               (let uu____5307 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____5307
                then
                  let uu____5308 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____5308 with
                  | (Some (true ),uu____5341)::uu____5342::[] ->
                      w FStar_Syntax_Util.t_true
                  | uu____5380::(Some (true ),uu____5381)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),uu____5419)::(uu____5420,(arg,uu____5422))::[]
                      -> arg
                  | (uu____5463,(arg,uu____5465))::(Some (false ),uu____5466)::[]
                      -> arg
                  | uu____5507 -> tm1
                else
                  (let uu____5517 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____5517
                   then
                     let uu____5518 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____5518 with
                     | uu____5551::(Some (true ),uu____5552)::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (false ),uu____5590)::uu____5591::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____5629)::(uu____5630,(arg,uu____5632))::[]
                         -> arg
                     | (uu____5673,(p,uu____5675))::(uu____5676,(q,uu____5678))::[]
                         ->
                         let uu____5720 = FStar_Syntax_Util.term_eq p q in
                         (if uu____5720
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____5722 -> tm1
                   else
                     (let uu____5732 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____5732
                      then
                        let uu____5733 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____5733 with
                        | (Some (true ),uu____5766)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____5790)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____5814 -> tm1
                      else
                        (let uu____5824 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid in
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
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5861 -> tm1)
                                | uu____5863 -> tm1)
                           | (uu____5864,Some (FStar_Syntax_Syntax.Implicit
                              uu____5865))::(t,uu____5867)::[] ->
                               let uu____5894 =
                                 let uu____5895 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5895.FStar_Syntax_Syntax.n in
                               (match uu____5894 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5898::[],body,uu____5900) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5916 -> tm1)
                                | uu____5918 -> tm1)
                           | uu____5919 -> tm1
                         else
                           (let uu____5926 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid in
                            if uu____5926
                            then
                              match args with
                              | (t,uu____5928)::[] ->
                                  let uu____5941 =
                                    let uu____5942 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5942.FStar_Syntax_Syntax.n in
                                  (match uu____5941 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5945::[],body,uu____5947) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5963 -> tm1)
                                   | uu____5965 -> tm1)
                              | (uu____5966,Some
                                 (FStar_Syntax_Syntax.Implicit uu____5967))::
                                  (t,uu____5969)::[] ->
                                  let uu____5996 =
                                    let uu____5997 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5997.FStar_Syntax_Syntax.n in
                                  (match uu____5996 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6000::[],body,uu____6002) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____6018 -> tm1)
                                   | uu____6020 -> tm1)
                              | uu____6021 -> tm1
                            else reduce_equality cfg tm1)))))
         | uu____6028 -> tm1)
let is_norm_request hd1 args =
  let uu____6043 =
    let uu____6047 =
      let uu____6048 = FStar_Syntax_Util.un_uinst hd1 in
      uu____6048.FStar_Syntax_Syntax.n in
    (uu____6047, args) in
  match uu____6043 with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6053::uu____6054::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize_term
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6057::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize
  | uu____6059 -> false
let get_norm_request args =
  match args with
  | uu____6078::(tm,uu____6080)::[] -> tm
  | (tm,uu____6090)::[] -> tm
  | uu____6095 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___143_6102  ->
    match uu___143_6102 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.tk = uu____6104;
           FStar_Syntax_Syntax.pos = uu____6105;
           FStar_Syntax_Syntax.vars = uu____6106;_},uu____6107,uu____6108))::uu____6109
        -> true
    | uu____6115 -> false
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
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____6259 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____6268 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____6269 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6270;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____6271;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6276;
                 FStar_Syntax_Syntax.fv_delta = uu____6277;
                 FStar_Syntax_Syntax.fv_qual = Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6281;
                 FStar_Syntax_Syntax.fv_delta = uu____6282;
                 FStar_Syntax_Syntax.fv_qual = Some
                   (FStar_Syntax_Syntax.Record_ctor uu____6283);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (FStar_Syntax_Util.is_fstar_tactics_embed hd1) ||
                 (FStar_Syntax_Util.is_fstar_tactics_by_tactic hd1)
               ->
               let args1 = closures_as_args_delayed cfg env args in
               let hd2 = closure_as_term cfg env hd1 in
               let t2 =
                 let uu___169_6316 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.tk =
                     (uu___169_6316.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___169_6316.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___169_6316.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____6342 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____6342) && (is_norm_request hd1 args))
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
                 let uu___170_6355 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___170_6355.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___170_6355.primitive_steps)
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
                  FStar_Syntax_Syntax.tk = uu____6360;
                  FStar_Syntax_Syntax.pos = uu____6361;
                  FStar_Syntax_Syntax.vars = uu____6362;_},a1::a2::rest)
               ->
               let uu____6396 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6396 with
                | (hd1,uu____6407) ->
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
                    (FStar_Const.Const_reflect uu____6462);
                  FStar_Syntax_Syntax.tk = uu____6463;
                  FStar_Syntax_Syntax.pos = uu____6464;
                  FStar_Syntax_Syntax.vars = uu____6465;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____6488 = FStar_List.tl stack1 in
               norm cfg env uu____6488 (fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.tk = uu____6491;
                  FStar_Syntax_Syntax.pos = uu____6492;
                  FStar_Syntax_Syntax.vars = uu____6493;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____6516 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6516 with
                | (reify_head,uu____6527) ->
                    let a1 =
                      let uu____6543 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (fst a) in
                      FStar_Syntax_Subst.compress uu____6543 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____6546);
                            FStar_Syntax_Syntax.tk = uu____6547;
                            FStar_Syntax_Syntax.pos = uu____6548;
                            FStar_Syntax_Syntax.vars = uu____6549;_},a2::[])
                         -> norm cfg env stack1 (fst a2)
                     | uu____6574 ->
                         let stack2 =
                           (App
                              (reify_head, None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____6582 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____6582
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____6589 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____6589
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____6592 =
                      let uu____6596 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____6596, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____6592 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___144_6605  ->
                         match uu___144_6605 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____6608 =
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
                 if uu____6608 then false else should_delta in
               if Prims.op_Negation should_delta1
               then rebuild cfg env stack1 t1
               else
                 (let r_env =
                    let uu____6612 = FStar_Syntax_Syntax.range_of_fv f in
                    FStar_TypeChecker_Env.set_range cfg.tcenv uu____6612 in
                  let uu____6613 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  match uu____6613 with
                  | None  ->
                      (log cfg
                         (fun uu____6624  ->
                            FStar_Util.print "Tm_fvar case 2\n" []);
                       rebuild cfg env stack1 t1)
                  | Some (us,t2) ->
                      (log cfg
                         (fun uu____6630  ->
                            let uu____6631 =
                              FStar_Syntax_Print.term_to_string t0 in
                            let uu____6632 =
                              FStar_Syntax_Print.term_to_string t2 in
                            FStar_Util.print2 ">>> Unfolded %s to %s\n"
                              uu____6631 uu____6632);
                       (let t3 =
                          let uu____6634 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 (UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant)) in
                          if uu____6634
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
                          | (UnivArgs (us',uu____6646))::stack2 ->
                              let env1 =
                                FStar_All.pipe_right us'
                                  (FStar_List.fold_left
                                     (fun env1  -> fun u  -> (Univ u) :: env1)
                                     env) in
                              norm cfg env1 stack2 t3
                          | uu____6659 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack1 t3
                          | uu____6660 ->
                              let uu____6661 =
                                let uu____6662 =
                                  FStar_Syntax_Print.lid_to_string
                                    (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                FStar_Util.format1
                                  "Impossible: missing universe instantiation on %s"
                                  uu____6662 in
                              failwith uu____6661
                        else norm cfg env stack1 t3)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____6669 = lookup_bvar env x in
               (match uu____6669 with
                | Univ uu____6670 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____6685 = FStar_ST.read r in
                      (match uu____6685 with
                       | Some (env2,t') ->
                           (log cfg
                              (fun uu____6704  ->
                                 let uu____6705 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____6706 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____6705
                                   uu____6706);
                            (let uu____6707 =
                               let uu____6708 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____6708.FStar_Syntax_Syntax.n in
                             match uu____6707 with
                             | FStar_Syntax_Syntax.Tm_abs uu____6711 ->
                                 norm cfg env2 stack1 t'
                             | uu____6721 -> rebuild cfg env2 stack1 t'))
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
                                      (fun uu____6773  ->
                                         let uu____6774 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6774);
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
                                           (fun uu___145_6777  ->
                                              match uu___145_6777 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____6778 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____6780  ->
                                         let uu____6781 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6781);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____6782 when
                                   FStar_All.pipe_right cfg.steps
                                     (FStar_List.contains Reify)
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____6784 ->
                                   let cfg1 =
                                     let uu___171_6787 = cfg in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___171_6787.tcenv);
                                       delta_level =
                                         (uu___171_6787.delta_level);
                                       primitive_steps =
                                         (uu___171_6787.primitive_steps)
                                     } in
                                   let uu____6788 =
                                     closure_as_term cfg1 env t1 in
                                   rebuild cfg1 env stack1 uu____6788)
                          | uu____6789::tl1 ->
                              (log cfg
                                 (fun uu____6799  ->
                                    let uu____6800 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____6800);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___172_6819 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___172_6819.tcenv);
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
                             | Some rc ->
                                 let uu____6850 =
                                   let uu___173_6851 = rc in
                                   let uu____6852 =
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                   {
                                     FStar_Syntax_Syntax.residual_effect =
                                       (uu___173_6851.FStar_Syntax_Syntax.residual_effect);
                                     FStar_Syntax_Syntax.residual_typ =
                                       uu____6852;
                                     FStar_Syntax_Syntax.residual_flags =
                                       (uu___173_6851.FStar_Syntax_Syntax.residual_flags)
                                   } in
                                 Some uu____6850
                             | uu____6858 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____6867  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____6872  ->
                                 let uu____6873 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____6873);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___174_6883 = cfg in
                               let uu____6884 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___174_6883.steps);
                                 tcenv = (uu___174_6883.tcenv);
                                 delta_level = (uu___174_6883.delta_level);
                                 primitive_steps = uu____6884
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____6889)::uu____6890 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____6894 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____6894
                    else
                      (let uu____6896 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____6896 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some rc ->
                                 let uu____6907 =
                                   let uu___173_6908 = rc in
                                   let uu____6909 =
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                   {
                                     FStar_Syntax_Syntax.residual_effect =
                                       (uu___173_6908.FStar_Syntax_Syntax.residual_effect);
                                     FStar_Syntax_Syntax.residual_typ =
                                       uu____6909;
                                     FStar_Syntax_Syntax.residual_flags =
                                       (uu___173_6908.FStar_Syntax_Syntax.residual_flags)
                                   } in
                                 Some uu____6907
                             | uu____6915 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____6924  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____6929  ->
                                 let uu____6930 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____6930);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___174_6940 = cfg in
                               let uu____6941 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___174_6940.steps);
                                 tcenv = (uu___174_6940.tcenv);
                                 delta_level = (uu___174_6940.delta_level);
                                 primitive_steps = uu____6941
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____6946)::uu____6947 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____6953 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____6953
                    else
                      (let uu____6955 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____6955 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some rc ->
                                 let uu____6966 =
                                   let uu___173_6967 = rc in
                                   let uu____6968 =
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                   {
                                     FStar_Syntax_Syntax.residual_effect =
                                       (uu___173_6967.FStar_Syntax_Syntax.residual_effect);
                                     FStar_Syntax_Syntax.residual_typ =
                                       uu____6968;
                                     FStar_Syntax_Syntax.residual_flags =
                                       (uu___173_6967.FStar_Syntax_Syntax.residual_flags)
                                   } in
                                 Some uu____6966
                             | uu____6974 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____6983  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____6988  ->
                                 let uu____6989 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____6989);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___174_6999 = cfg in
                               let uu____7000 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___174_6999.steps);
                                 tcenv = (uu___174_6999.tcenv);
                                 delta_level = (uu___174_6999.delta_level);
                                 primitive_steps = uu____7000
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____7005)::uu____7006 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7011 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7011
                    else
                      (let uu____7013 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7013 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some rc ->
                                 let uu____7024 =
                                   let uu___173_7025 = rc in
                                   let uu____7026 =
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                   {
                                     FStar_Syntax_Syntax.residual_effect =
                                       (uu___173_7025.FStar_Syntax_Syntax.residual_effect);
                                     FStar_Syntax_Syntax.residual_typ =
                                       uu____7026;
                                     FStar_Syntax_Syntax.residual_flags =
                                       (uu___173_7025.FStar_Syntax_Syntax.residual_flags)
                                   } in
                                 Some uu____7024
                             | uu____7032 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7041  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7046  ->
                                 let uu____7047 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7047);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___174_7057 = cfg in
                               let uu____7058 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___174_7057.steps);
                                 tcenv = (uu___174_7057.tcenv);
                                 delta_level = (uu___174_7057.delta_level);
                                 primitive_steps = uu____7058
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____7063)::uu____7064 ->
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
                             | Some rc ->
                                 let uu____7085 =
                                   let uu___173_7086 = rc in
                                   let uu____7087 =
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                   {
                                     FStar_Syntax_Syntax.residual_effect =
                                       (uu___173_7086.FStar_Syntax_Syntax.residual_effect);
                                     FStar_Syntax_Syntax.residual_typ =
                                       uu____7087;
                                     FStar_Syntax_Syntax.residual_flags =
                                       (uu___173_7086.FStar_Syntax_Syntax.residual_flags)
                                   } in
                                 Some uu____7085
                             | uu____7093 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7102  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7107  ->
                                 let uu____7108 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7108);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___174_7118 = cfg in
                               let uu____7119 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___174_7118.steps);
                                 tcenv = (uu___174_7118.tcenv);
                                 delta_level = (uu___174_7118.delta_level);
                                 primitive_steps = uu____7119
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7124 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7124
                    else
                      (let uu____7126 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7126 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some rc ->
                                 let uu____7137 =
                                   let uu___173_7138 = rc in
                                   let uu____7139 =
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                   {
                                     FStar_Syntax_Syntax.residual_effect =
                                       (uu___173_7138.FStar_Syntax_Syntax.residual_effect);
                                     FStar_Syntax_Syntax.residual_typ =
                                       uu____7139;
                                     FStar_Syntax_Syntax.residual_flags =
                                       (uu___173_7138.FStar_Syntax_Syntax.residual_flags)
                                   } in
                                 Some uu____7137
                             | uu____7145 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7154  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7159  ->
                                 let uu____7160 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7160);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___174_7170 = cfg in
                               let uu____7171 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___174_7170.steps);
                                 tcenv = (uu___174_7170.tcenv);
                                 delta_level = (uu___174_7170.delta_level);
                                 primitive_steps = uu____7171
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
                      (fun uu____7198  ->
                         fun stack2  ->
                           match uu____7198 with
                           | (a,aq) ->
                               let uu____7206 =
                                 let uu____7207 =
                                   let uu____7211 =
                                     let uu____7212 =
                                       let uu____7222 =
                                         FStar_Util.mk_ref None in
                                       (env, a, uu____7222, false) in
                                     Clos uu____7212 in
                                   (uu____7211, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____7207 in
                               uu____7206 :: stack2) args) in
               (log cfg
                  (fun uu____7244  ->
                     let uu____7245 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____7245);
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
                             ((let uu___175_7266 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___175_7266.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___175_7266.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____7267 ->
                      let uu____7270 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7270)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____7273 = FStar_Syntax_Subst.open_term [(x, None)] f in
                  match uu____7273 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____7289 =
                          let uu____7290 =
                            let uu____7295 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___176_7296 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___176_7296.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___176_7296.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____7295) in
                          FStar_Syntax_Syntax.Tm_refine uu____7290 in
                        mk uu____7289 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____7309 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____7309
               else
                 (let uu____7311 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____7311 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____7317 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  -> fun uu____7323  -> Dummy :: env1)
                               env) in
                        norm_comp cfg uu____7317 c1 in
                      let t2 =
                        let uu____7330 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____7330 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____7373)::uu____7374 -> norm cfg env stack1 t11
                | (Arg uu____7379)::uu____7380 -> norm cfg env stack1 t11
                | (App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.tk = uu____7385;
                       FStar_Syntax_Syntax.pos = uu____7386;
                       FStar_Syntax_Syntax.vars = uu____7387;_},uu____7388,uu____7389))::uu____7390
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____7396)::uu____7397 ->
                    norm cfg env stack1 t11
                | uu____7402 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____7405  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____7418 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____7418
                        | FStar_Util.Inr c ->
                            let uu____7426 = norm_comp cfg env c in
                            FStar_Util.Inr uu____7426 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____7431 =
                        mk
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (t12, (tc1, tacopt1), l))
                          t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____7431)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____7482,{
                              FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                uu____7483;
                              FStar_Syntax_Syntax.lbunivs = uu____7484;
                              FStar_Syntax_Syntax.lbtyp = uu____7485;
                              FStar_Syntax_Syntax.lbeff = uu____7486;
                              FStar_Syntax_Syntax.lbdef = uu____7487;_}::uu____7488),uu____7489)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____7515 =
                 (let uu____7516 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____7516) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____7517 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____7517))) in
               if uu____7515
               then
                 let env1 =
                   let uu____7520 =
                     let uu____7521 =
                       let uu____7531 = FStar_Util.mk_ref None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____7531,
                         false) in
                     Clos uu____7521 in
                   uu____7520 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____7555 =
                    let uu____7558 =
                      let uu____7559 =
                        let uu____7560 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____7560
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____7559] in
                    FStar_Syntax_Subst.open_term uu____7558 body in
                  match uu____7555 with
                  | (bs,body1) ->
                      let lb1 =
                        let uu___177_7566 = lb in
                        let uu____7567 =
                          let uu____7570 =
                            let uu____7571 = FStar_List.hd bs in
                            FStar_All.pipe_right uu____7571
                              FStar_Pervasives.fst in
                          FStar_All.pipe_right uu____7570
                            (fun _0_41  -> FStar_Util.Inl _0_41) in
                        let uu____7580 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____7583 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = uu____7567;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___177_7566.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____7580;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___177_7566.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____7583
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____7593  -> Dummy :: env1)
                             env) in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____7609 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____7609
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____7622 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____7644  ->
                        match uu____7644 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____7683 =
                                let uu___178_7684 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___178_7684.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___178_7684.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____7683 in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos in
                            let memo = FStar_Util.mk_ref None in
                            let rec_env1 = (Clos (env, fix_f_i, memo, true))
                              :: rec_env in
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1")))) (snd lbs)
                   (env, [], (Prims.parse_int "0")) in
               (match uu____7622 with
                | (rec_env,memos,uu____7744) ->
                    let uu____7759 =
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
                             let uu____7801 =
                               let uu____7802 =
                                 let uu____7812 = FStar_Util.mk_ref None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____7812, false) in
                               Clos uu____7802 in
                             uu____7801 :: env1) (snd lbs) env in
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
                             FStar_Syntax_Syntax.tk = uu____7850;
                             FStar_Syntax_Syntax.pos = uu____7851;
                             FStar_Syntax_Syntax.vars = uu____7852;_},uu____7853,uu____7854))::uu____7855
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____7861 -> false in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____7868 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____7868
                        then
                          let uu___179_7869 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___179_7869.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps = (uu___179_7869.primitive_steps)
                          }
                        else
                          (let uu___180_7871 = cfg in
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___180_7871.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta];
                             primitive_steps =
                               (uu___180_7871.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____7873 =
                         let uu____7874 = FStar_Syntax_Subst.compress head1 in
                         uu____7874.FStar_Syntax_Syntax.n in
                       match uu____7873 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____7888 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____7888 with
                            | (uu____7889,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____7893 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____7900 =
                                         let uu____7901 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____7901.FStar_Syntax_Syntax.n in
                                       match uu____7900 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____7906,uu____7907))
                                           ->
                                           let uu____7916 =
                                             let uu____7917 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____7917.FStar_Syntax_Syntax.n in
                                           (match uu____7916 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____7922,msrc,uu____7924))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____7933 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                Some uu____7933
                                            | uu____7934 -> None)
                                       | uu____7935 -> None in
                                     let uu____7936 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____7936 with
                                      | Some e ->
                                          let lb1 =
                                            let uu___181_7940 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___181_7940.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___181_7940.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___181_7940.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Syntax_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____7941 =
                                            FStar_List.tl stack1 in
                                          let uu____7942 =
                                            let uu____7943 =
                                              let uu____7946 =
                                                let uu____7947 =
                                                  let uu____7955 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____7955) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____7947 in
                                              FStar_Syntax_Syntax.mk
                                                uu____7946 in
                                            uu____7943 None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____7941 uu____7942
                                      | None  ->
                                          let uu____7972 =
                                            let uu____7973 = is_return body in
                                            match uu____7973 with
                                            | Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____7976;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____7977;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____7978;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____7983 -> false in
                                          if uu____7972
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
                                               let uu____8006 =
                                                 let uu____8009 =
                                                   let uu____8010 =
                                                     let uu____8020 =
                                                       let uu____8022 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____8022] in
                                                     (uu____8020, body1,
                                                       (Some body_rc)) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____8010 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8009 in
                                               uu____8006 None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____8041 =
                                                 let uu____8042 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____8042.FStar_Syntax_Syntax.n in
                                               match uu____8041 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____8048::uu____8049::[])
                                                   ->
                                                   let uu____8055 =
                                                     let uu____8058 =
                                                       let uu____8059 =
                                                         let uu____8064 =
                                                           let uu____8066 =
                                                             let uu____8067 =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____8067 in
                                                           let uu____8068 =
                                                             let uu____8070 =
                                                               let uu____8071
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____8071 in
                                                             [uu____8070] in
                                                           uu____8066 ::
                                                             uu____8068 in
                                                         (bind1, uu____8064) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____8059 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8058 in
                                                   uu____8055 None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____8083 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____8089 =
                                                 let uu____8092 =
                                                   let uu____8093 =
                                                     let uu____8103 =
                                                       let uu____8105 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____8106 =
                                                         let uu____8108 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____8109 =
                                                           let uu____8111 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____8112 =
                                                             let uu____8114 =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____8115 =
                                                               let uu____8117
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____8118
                                                                 =
                                                                 let uu____8120
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____8120] in
                                                               uu____8117 ::
                                                                 uu____8118 in
                                                             uu____8114 ::
                                                               uu____8115 in
                                                           uu____8111 ::
                                                             uu____8112 in
                                                         uu____8108 ::
                                                           uu____8109 in
                                                       uu____8105 ::
                                                         uu____8106 in
                                                     (bind_inst, uu____8103) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____8093 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8092 in
                                               uu____8089 None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____8132 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____8132 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____8150 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8150 with
                            | (uu____8151,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____8174 =
                                        let uu____8175 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____8175.FStar_Syntax_Syntax.n in
                                      match uu____8174 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____8181) -> t4
                                      | uu____8186 -> head2 in
                                    let uu____8187 =
                                      let uu____8188 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____8188.FStar_Syntax_Syntax.n in
                                    match uu____8187 with
                                    | FStar_Syntax_Syntax.Tm_fvar x -> Some x
                                    | uu____8193 -> None in
                                  let uu____8194 = maybe_extract_fv head2 in
                                  match uu____8194 with
                                  | Some x when
                                      let uu____8200 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____8200
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____8204 =
                                          maybe_extract_fv head3 in
                                        match uu____8204 with
                                        | Some uu____8207 -> Some true
                                        | uu____8208 -> Some false in
                                      (head3, action_unfolded)
                                  | uu____8211 -> (head2, None) in
                                ((let is_arg_impure uu____8222 =
                                    match uu____8222 with
                                    | (e,q) ->
                                        let uu____8227 =
                                          let uu____8228 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____8228.FStar_Syntax_Syntax.n in
                                        (match uu____8227 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____8243 -> false) in
                                  let uu____8244 =
                                    let uu____8245 =
                                      let uu____8249 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____8249 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____8245 in
                                  if uu____8244
                                  then
                                    let uu____8252 =
                                      let uu____8253 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____8253 in
                                    failwith uu____8252
                                  else ());
                                 (let uu____8255 =
                                    maybe_unfold_action head_app in
                                  match uu____8255 with
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
                                      let uu____8290 = FStar_List.tl stack1 in
                                      norm cfg env uu____8290 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____8304 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____8304 in
                           let uu____8305 = FStar_List.tl stack1 in
                           norm cfg env uu____8305 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____8388  ->
                                     match uu____8388 with
                                     | (pat,wopt,tm) ->
                                         let uu____8426 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____8426))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____8452 = FStar_List.tl stack1 in
                           norm cfg env uu____8452 tm
                       | uu____8453 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.tk = uu____8462;
                             FStar_Syntax_Syntax.pos = uu____8463;
                             FStar_Syntax_Syntax.vars = uu____8464;_},uu____8465,uu____8466))::uu____8467
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____8473 -> false in
                    if should_reify
                    then
                      let uu____8474 = FStar_List.tl stack1 in
                      let uu____8475 =
                        let uu____8476 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____8476 in
                      norm cfg env uu____8474 uu____8475
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____8479 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____8479
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___182_8485 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___182_8485.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___182_8485.primitive_steps)
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
                | uu____8487 ->
                    (match stack1 with
                     | uu____8488::uu____8489 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____8493)
                              -> norm cfg env ((Meta (m, r)) :: stack1) head1
                          | FStar_Syntax_Syntax.Meta_pattern args ->
                              let args1 = norm_pattern_args cfg env args in
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_pattern args1),
                                      (t1.FStar_Syntax_Syntax.pos))) ::
                                stack1) head1
                          | uu____8508 -> norm cfg env stack1 head1)
                     | [] ->
                         let head2 = norm cfg env [] head1 in
                         let m1 =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               let uu____8518 =
                                 norm_pattern_args cfg env args in
                               FStar_Syntax_Syntax.Meta_pattern uu____8518
                           | uu____8525 -> m in
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
              let uu____8537 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____8537 with
              | (uu____8538,return_repr) ->
                  let return_inst =
                    let uu____8545 =
                      let uu____8546 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____8546.FStar_Syntax_Syntax.n in
                    match uu____8545 with
                    | FStar_Syntax_Syntax.Tm_uinst (return_tm,uu____8552::[])
                        ->
                        let uu____8558 =
                          let uu____8561 =
                            let uu____8562 =
                              let uu____8567 =
                                let uu____8569 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____8569] in
                              (return_tm, uu____8567) in
                            FStar_Syntax_Syntax.Tm_uinst uu____8562 in
                          FStar_Syntax_Syntax.mk uu____8561 in
                        uu____8558 None e.FStar_Syntax_Syntax.pos
                    | uu____8581 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____8584 =
                    let uu____8587 =
                      let uu____8588 =
                        let uu____8598 =
                          let uu____8600 = FStar_Syntax_Syntax.as_arg t in
                          let uu____8601 =
                            let uu____8603 = FStar_Syntax_Syntax.as_arg e in
                            [uu____8603] in
                          uu____8600 :: uu____8601 in
                        (return_inst, uu____8598) in
                      FStar_Syntax_Syntax.Tm_app uu____8588 in
                    FStar_Syntax_Syntax.mk uu____8587 in
                  uu____8584 None e.FStar_Syntax_Syntax.pos
            else
              (let uu____8616 = FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____8616 with
               | None  ->
                   let uu____8618 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____8618
               | Some
                   { FStar_TypeChecker_Env.msource = uu____8619;
                     FStar_TypeChecker_Env.mtarget = uu____8620;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____8621;
                         FStar_TypeChecker_Env.mlift_term = None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | Some
                   { FStar_TypeChecker_Env.msource = uu____8632;
                     FStar_TypeChecker_Env.mtarget = uu____8633;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____8634;
                         FStar_TypeChecker_Env.mlift_term = Some lift;_};_}
                   ->
                   let uu____8652 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____8652)
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
                (fun uu____8682  ->
                   match uu____8682 with
                   | (a,imp) ->
                       let uu____8689 = norm cfg env [] a in
                       (uu____8689, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___183_8704 = comp1 in
            let uu____8707 =
              let uu____8708 =
                let uu____8714 = norm cfg env [] t in
                let uu____8715 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____8714, uu____8715) in
              FStar_Syntax_Syntax.Total uu____8708 in
            {
              FStar_Syntax_Syntax.n = uu____8707;
              FStar_Syntax_Syntax.tk = (uu___183_8704.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___183_8704.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___183_8704.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___184_8730 = comp1 in
            let uu____8733 =
              let uu____8734 =
                let uu____8740 = norm cfg env [] t in
                let uu____8741 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____8740, uu____8741) in
              FStar_Syntax_Syntax.GTotal uu____8734 in
            {
              FStar_Syntax_Syntax.n = uu____8733;
              FStar_Syntax_Syntax.tk = (uu___184_8730.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___184_8730.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___184_8730.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____8772  ->
                      match uu____8772 with
                      | (a,i) ->
                          let uu____8779 = norm cfg env [] a in
                          (uu____8779, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___146_8784  ->
                      match uu___146_8784 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____8788 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____8788
                      | f -> f)) in
            let uu___185_8792 = comp1 in
            let uu____8795 =
              let uu____8796 =
                let uu___186_8797 = ct in
                let uu____8798 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____8799 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____8802 = norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____8798;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___186_8797.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____8799;
                  FStar_Syntax_Syntax.effect_args = uu____8802;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____8796 in
            {
              FStar_Syntax_Syntax.n = uu____8795;
              FStar_Syntax_Syntax.tk = (uu___185_8792.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___185_8792.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___185_8792.FStar_Syntax_Syntax.vars)
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
            (let uu___187_8819 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___187_8819.tcenv);
               delta_level = (uu___187_8819.delta_level);
               primitive_steps = (uu___187_8819.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____8824 = norm1 t in
          FStar_Syntax_Util.non_informative uu____8824 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____8827 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___188_8841 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.tk = (uu___188_8841.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___188_8841.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___188_8841.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____8851 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____8851
            then
              let ct1 =
                match downgrade_ghost_effect_name
                        ct.FStar_Syntax_Syntax.effect_name
                with
                | Some pure_eff ->
                    let uu___189_8856 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___189_8856.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___189_8856.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___189_8856.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___189_8856.FStar_Syntax_Syntax.flags)
                    }
                | None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___190_8858 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___190_8858.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Syntax_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___190_8858.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___190_8858.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___190_8858.FStar_Syntax_Syntax.flags)
                    } in
              let uu___191_8859 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.tk =
                  (uu___191_8859.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___191_8859.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___191_8859.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____8865 -> c
and norm_binder:
  cfg ->
    env ->
      FStar_Syntax_Syntax.binder ->
        (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  =
  fun cfg  ->
    fun env  ->
      fun uu____8868  ->
        match uu____8868 with
        | (x,imp) ->
            let uu____8871 =
              let uu___192_8872 = x in
              let uu____8873 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___192_8872.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___192_8872.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____8873
              } in
            (uu____8871, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____8879 =
          FStar_List.fold_left
            (fun uu____8886  ->
               fun b  ->
                 match uu____8886 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____8879 with | (nbs,uu____8903) -> FStar_List.rev nbs
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
            let uu____8914 =
              let uu___193_8915 = rc in
              let uu____8916 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___193_8915.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____8916;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___193_8915.FStar_Syntax_Syntax.residual_flags)
              } in
            Some uu____8914
        | uu____8922 -> lopt
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
              ((let uu____8932 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____8932
                then
                  let uu____8933 = FStar_Syntax_Print.term_to_string tm in
                  let uu____8934 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2 "Normalized %s to %s\n" uu____8933
                    uu____8934
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___194_8945 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___194_8945.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____8965  ->
                    let uu____8966 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____8966);
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
              let uu____8997 =
                let uu___195_8998 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___195_8998.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___195_8998.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___195_8998.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____8997
          | (Arg (Univ uu____9003,uu____9004,uu____9005))::uu____9006 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____9008,uu____9009))::uu____9010 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____9022),aq,r))::stack2 ->
              (log cfg
                 (fun uu____9038  ->
                    let uu____9039 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____9039);
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
                 (let uu____9050 = FStar_ST.read m in
                  match uu____9050 with
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
                  | Some (uu____9076,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq) None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.extend_app head1 (t, aq) None r in
              let uu____9098 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____9098
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____9105  ->
                    let uu____9106 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____9106);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____9111 =
                  log cfg
                    (fun uu____9113  ->
                       let uu____9114 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____9115 =
                         let uu____9116 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____9123  ->
                                   match uu____9123 with
                                   | (p,uu____9129,uu____9130) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____9116
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____9114 uu____9115);
                  (let whnf = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___147_9140  ->
                               match uu___147_9140 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____9141 -> false)) in
                     let steps' =
                       let uu____9144 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____9144
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___196_9147 = cfg in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___196_9147.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___196_9147.primitive_steps)
                     } in
                   let norm_or_whnf env2 t1 =
                     if whnf
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____9181 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____9197 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____9231  ->
                                   fun uu____9232  ->
                                     match (uu____9231, uu____9232) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____9297 = norm_pat env3 p1 in
                                         (match uu____9297 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____9197 with
                          | (pats1,env3) ->
                              ((let uu___197_9363 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___197_9363.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___197_9363.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___198_9377 = x in
                           let uu____9378 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___198_9377.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___198_9377.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9378
                           } in
                         ((let uu___199_9384 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___199_9384.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___199_9384.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___200_9389 = x in
                           let uu____9390 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___200_9389.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___200_9389.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9390
                           } in
                         ((let uu___201_9396 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___201_9396.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___201_9396.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___202_9406 = x in
                           let uu____9407 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___202_9406.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___202_9406.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9407
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___203_9414 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.ty =
                               (uu___203_9414.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___203_9414.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf -> branches
                     | uu____9418 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____9421 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____9421 with
                                 | (p,wopt,e) ->
                                     let uu____9439 = norm_pat env1 p in
                                     (match uu____9439 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | None  -> None
                                            | Some w ->
                                                let uu____9463 =
                                                  norm_or_whnf env2 w in
                                                Some uu____9463 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____9468 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____9468) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____9478) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____9483 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____9484;
                        FStar_Syntax_Syntax.fv_delta = uu____9485;
                        FStar_Syntax_Syntax.fv_qual = Some
                          (FStar_Syntax_Syntax.Data_ctor );_}
                      -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____9489;
                        FStar_Syntax_Syntax.fv_delta = uu____9490;
                        FStar_Syntax_Syntax.fv_qual = Some
                          (FStar_Syntax_Syntax.Record_ctor uu____9491);_}
                      -> true
                  | uu____9498 -> false in
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
                  let uu____9597 = FStar_Syntax_Util.head_and_args scrutinee1 in
                  match uu____9597 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var uu____9629 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_wild uu____9631 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____9633 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee1.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____9645 ->
                                let uu____9646 =
                                  let uu____9647 = is_cons head1 in
                                  Prims.op_Negation uu____9647 in
                                FStar_Util.Inr uu____9646)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____9661 =
                             let uu____9662 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____9662.FStar_Syntax_Syntax.n in
                           (match uu____9661 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____9669 ->
                                let uu____9670 =
                                  let uu____9671 = is_cons head1 in
                                  Prims.op_Negation uu____9671 in
                                FStar_Util.Inr uu____9670))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____9705)::rest_a,(p1,uu____9708)::rest_p) ->
                      let uu____9736 = matches_pat t1 p1 in
                      (match uu____9736 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____9750 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____9821 = matches_pat scrutinee1 p1 in
                      (match uu____9821 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____9831  ->
                                 let uu____9832 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____9833 =
                                   let uu____9834 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____9834
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____9832 uu____9833);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____9843 =
                                        let uu____9844 =
                                          let uu____9854 =
                                            FStar_Util.mk_ref (Some ([], t1)) in
                                          ([], t1, uu____9854, false) in
                                        Clos uu____9844 in
                                      uu____9843 :: env2) env1 s in
                             let uu____9877 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____9877))) in
                let uu____9878 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____9878
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___148_9892  ->
                match uu___148_9892 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____9895 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____9899 -> d in
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
            let uu___204_9919 = config s e in
            {
              steps = (uu___204_9919.steps);
              tcenv = (uu___204_9919.tcenv);
              delta_level = (uu___204_9919.delta_level);
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
      fun t  -> let uu____9938 = config s e in norm_comp uu____9938 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  -> let uu____9945 = config [] env in norm_universe uu____9945 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun c  ->
      let uu____9952 = config [] env in ghost_to_pure_aux uu____9952 [] c
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
        let uu____9964 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____9964 in
      let uu____9965 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____9965
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | Some pure_eff ->
            let uu___205_9967 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___205_9967.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___205_9967.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____9968  ->
                    let uu____9969 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____9969))
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
            ((let uu____9982 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____9982);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____9991 = config [AllowUnboundUniverses] env in
          norm_comp uu____9991 [] c
        with
        | e ->
            ((let uu____9995 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____9995);
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
                   let uu____10032 =
                     let uu____10033 =
                       let uu____10038 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____10038) in
                     FStar_Syntax_Syntax.Tm_refine uu____10033 in
                   mk uu____10032 t01.FStar_Syntax_Syntax.pos
               | uu____10043 -> t2)
          | uu____10044 -> t2 in
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
        let uu____10066 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____10066 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____10082 ->
                 let uu____10086 = FStar_Syntax_Util.abs_formals e in
                 (match uu____10086 with
                  | (actuals,uu____10092,uu____10093) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____10105 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____10105 with
                         | (binders,args) ->
                             let uu____10115 =
                               FStar_Syntax_Syntax.mk_Tm_app e args None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____10115
                               (Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c)))))
let eta_expand:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____10124 =
        let uu____10128 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
        (uu____10128, (t.FStar_Syntax_Syntax.n)) in
      match uu____10124 with
      | (Some sort,uu____10135) ->
          let uu____10137 = mk sort t.FStar_Syntax_Syntax.pos in
          eta_expand_with_type env t uu____10137
      | (uu____10138,FStar_Syntax_Syntax.Tm_name x) ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____10142 ->
          let uu____10146 = FStar_Syntax_Util.head_and_args t in
          (match uu____10146 with
           | (head1,args) ->
               let uu____10172 =
                 let uu____10173 = FStar_Syntax_Subst.compress head1 in
                 uu____10173.FStar_Syntax_Syntax.n in
               (match uu____10172 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____10176,thead) ->
                    let uu____10190 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____10190 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____10221 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___210_10225 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___210_10225.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___210_10225.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___210_10225.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___210_10225.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___210_10225.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___210_10225.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ = None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___210_10225.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___210_10225.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___210_10225.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___210_10225.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___210_10225.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___210_10225.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___210_10225.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___210_10225.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___210_10225.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___210_10225.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___210_10225.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___210_10225.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___210_10225.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___210_10225.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___210_10225.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___210_10225.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___210_10225.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___210_10225.FStar_TypeChecker_Env.is_native_tactic)
                                 }) t in
                            match uu____10221 with
                            | (uu____10226,ty,uu____10228) ->
                                eta_expand_with_type env t ty))
                | uu____10229 ->
                    let uu____10230 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___211_10234 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___211_10234.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___211_10234.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___211_10234.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___211_10234.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___211_10234.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___211_10234.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ = None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___211_10234.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___211_10234.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___211_10234.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___211_10234.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___211_10234.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___211_10234.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___211_10234.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___211_10234.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___211_10234.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___211_10234.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___211_10234.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___211_10234.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___211_10234.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___211_10234.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___211_10234.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___211_10234.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___211_10234.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___211_10234.FStar_TypeChecker_Env.is_native_tactic)
                         }) t in
                    (match uu____10230 with
                     | (uu____10235,ty,uu____10237) ->
                         eta_expand_with_type env t ty)))